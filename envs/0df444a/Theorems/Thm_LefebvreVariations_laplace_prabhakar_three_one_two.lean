-- Prove2me | Theorems.Thm_LefebvreVariations_laplace_prabhakar_three_one_two
-- name    : LefebvreVariations.laplace_prabhakar_three_one_two
-- status  : Open
-- author  : @Secousses
-- created : 2026-11-26T21:34:24.399148+00:00
-- url     : https://prove2.me/theorems/01c20f2e-3832-42a0-997f-59c1142165d1
-- title:
--   Lefebvre's variations, No. 182 — on a theme by Prabhakar: the Laplace transform of the Prabhakar function with alpha equal to 3 and gamma equal to 2
-- statement:
--   For every real $c$ and every complex $s$ with $\operatorname{Re}s>|c|^{1/3}$,
--   $$
--   \int_0^\infty e^{-st}\,E^{2}_{3,1}\!\bigl(-c\,t^{3}\bigr)\,dt\;=\;\frac{s^{5}}{(s^{3}+c)^{2}},
--   $$
--   where $E^{\gamma}_{\alpha,\beta}(x)=\sum_{k\ge0}\dfrac{(\gamma)_k\,x^k}{k!\,\Gamma(\alpha k+\beta)}$ is the Prabhakar (three-parameter Mittag-Leffler) function and $(\gamma)_k=\gamma(\gamma+1)\cdots(\gamma+k-1)$. This is the case $(\alpha,\beta,\gamma)=(3,1,2)$ of the formula $\mathcal L\bigl[t^{\beta-1}E^{\gamma}_{\alpha,\beta}(-\lambda t^{\alpha})\bigr](s)=\dfrac{s^{\alpha\gamma-\beta}}{(s^{\alpha}+\lambda)^{\gamma}}$. Termwise, $\sum_k (k+1)(-c)^k s^{-3k-1}=s^{-1}(1+c\,s^{-3})^{-2}$.
--
--   **Formalization Note** In Lean, `FractionalCalc.prabhakar α β γ x = ∑' k, (∏ j < k, (γ + j)) * x ^ k / (k! * Real.Gamma (α * k + β))`, and `laplace` integrates over `(0, ∞)`. The statement is `FractionalCalc.laplace_prabhakar` at `α = 3`, `β = 1`, `γ = 2` (so `t ^ (β - 1) = t ^ 0`, written as in the parent), with the parent's hypothesis `|c| ^ (1/α) < s.re`. All powers of `s` are complex powers with real exponents `5`, `3`, `2`, which are integers, so no branch choice enters.
--
--   **Why this is a variation.** This varies the open platform problem `FractionalCalc.laplace_prabhakar`, the Laplace transform of $t^{\beta-1}E^{\gamma}_{\alpha,\beta}(-\lambda t^{\alpha})$ for all $\alpha>0$. The platform has a proved version only for $\alpha\le2$ (`laplace_prabhakar_of_le_two`); this is the first explicit case beyond that range, $(\alpha,\beta,\gamma)=(3,1,2)$, where $E^{2}_{3,1}(x)=\sum_k (k+1)x^k/(3k)!$ and the transform is $s^{5}/(s^{3}+c)^{2}$ for $\mathrm{Re}\,s>|c|^{1/3}$. The exponent $\gamma=2$ is an integer, so the complex powers have no branch ambiguity.
--
--   **Attribution.** This statement belongs to *Lefebvre's variations*, a series proposed by Erwan Lefebvre: each variation plays an open problem of the platform at its first non-trivial size, so that it can be settled and then reused to attack the open problem itself.
-- source:
--   A. Prabhakar, A singular integral equation with a generalized Mittag-Leffler function in the kernel, Yokohama Math. J. 19 (1971) 7-15; A. A. Kilbas, M. Saigo, R. K. Saxena, Generalized Mittag-Leffler function and generalized fractional calculus operators, Integral Transforms Spec. Funct. 15 (2004) 31-49 (both cited from memory; page numbers not verified). Origin of this statement: the case (alpha, beta, gamma) = (3, 1, 2) of the platform theorem FractionalCalc.laplace_prabhakar (Eq. 27); the platform's proved variant covers only alpha <= 2. The identity was checked numerically (mpmath, series for E^2_{3,1}, c = -1, 2, -8, s = |c|^{1/3} + 1.5): agreement to 8 or more digits.

import Mathlib
import Definitions.Def_FractionalCalc_rlIntegral
import Definitions.Def_FractionalCalc_caputoDeriv
import Definitions.Def_FractionalCalc_rlDeriv
import Definitions.Def_FractionalCalc_mittagLeffler
import Definitions.Def_QueueingFundamentals_Transient_laplace

set_option autoImplicit false

open MeasureTheory Set Classical QueueingFundamentals.Transient

namespace LefebvreVariations

/-- **A Prabhakar function with `α = 3`.** For `α = 3`, `β = 1`, `γ = 2`, every real `c` and every complex
`s` with `Re s > |c|^{1/3}`,
`L[ E^{2}_{3,1}(-c t³) ](s) = s^{5} / (s³ + c)²`,
the case `α = 3 > 2` of the Laplace transform of `t^{β-1} E^γ_{α,β}(-λ t^α)` (Prabhakar, Yokohama Math. J. 19
(1971) 7–15; Kilbas–Saigo–Saxena, Integral Transforms Spec. Funct. 15 (2004) 31–49; both cited from memory).
Termwise, `Σ_k (2)_k (-c)^k s^{-3k-1} / k! = s^{-1}(1 + c s^{-3})^{-2}`.

**Formalization Note.** Same `prabhakar` and `laplace` as `FractionalCalc.laplace_prabhakar`, at
`(α, β, γ) = (3, 1, 2)`; the exponent `γ = 2` is an integer, so the complex power of `s³ + c` has no branch
ambiguity, which is why this case is stated beyond the range `α ≤ 2` where the formula holds for all `γ`. -/
theorem laplace_prabhakar_three_one_two (c : ℝ) (s : ℂ) (hs : |c| ^ (1 / (3 : ℝ)) < s.re) :
    laplace (fun t => t ^ ((1 : ℝ) - 1) * FractionalCalc.prabhakar 3 1 2 (-c * t ^ (3 : ℝ))) s =
      s ^ ((3 : ℝ) * 2 - 1 : ℂ) / (s ^ ((3 : ℝ) : ℂ) + c) ^ ((2 : ℝ) : ℂ) := by
  sorry

end LefebvreVariations
