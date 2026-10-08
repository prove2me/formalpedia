-- Prove2me | Theorems.Thm_OptimalRLS_Minimax_proposition_4_kl
-- name    : OptimalRLS.Minimax.proposition_4_kl
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-05T19:31:21.95362+00:00
-- url     : https://prove2.me/theorems/9ca4a2c9-7fbf-4bed-bb80-d574fe033aea
-- title:
--   Proposition 4, (54), p. 21 — K(ρ_f, ρ_f′) ≤ (16/(15dL²)) ‖√T(f − f′)‖²
-- statement:
--   Work in the setting of §5.3 as in the first part of Proposition 4: $\dim Y = d < \infty$, Hypothesis 1 with constant $\kappa$, positive $R, \alpha, \beta$, $1 < b$, $1 \le c \le 2$, and a probability measure $\nu$ on $X$ whose operator $T = \sum_{n\ge1} t_n\langle\cdot,e_n\rangle e_n$ has decreasing eigenvalues with $\alpha \le n^b t_n \le \beta$. Let $(v_j)_{j=1}^d$ be an orthonormal basis of $Y$ and $L = 4\sqrt{\kappa^c R}$.
--
--   If $f = T^{(c-1)/2} g$ and $f' = T^{(c-1)/2} g'$ with $g, g' \in \mathcal H$, $\|g\|^2 \le R$ and $\|g'\|^2 \le R$, then the Kullback–Leibler information of the two model distributions of Proposition 4 satisfies
--   $$\mathcal K(\rho_f, \rho_{f'}) \le \frac{16}{15\, d L^2}\, \big\|\sqrt T (f - f')\big\|_{\mathcal H}^2 \qquad (54),$$
--   where $\|\sqrt T h\|^2_{\mathcal H} = \int_X \|h(x)\|_Y^2\, d\nu(x)$ and $\mathcal K(\rho_1, \rho_2) = \int \log \frac{d\rho_1}{d\rho_2}\, d\rho_1$.
--
--   This bound converts the separation of the hypotheses in the $\sqrt T$-norm into a bound on their statistical distinguishability, which is the input of the Fano-type argument of Theorem 5.
--
--   **Formalization Note.** The KL information is Mathlib's `InformationTheory.klDiv`, valued in $[0, \infty]$ (it is $+\infty$ when $\rho_f$ is not absolutely continuous with respect to $\rho_{f'}$), so the inequality is between extended nonnegative reals. The page's second hypothesis reads "$\|g\|^2 \le R$"; it is read as $\|g'\|^2 \le R$, the evident intent. $\|\sqrt T h\|^2$ is `covForm ν h h`.
-- source:
--   Caponnetto & De Vito, Found. Comput. Math. 7 (2007), authors' copy, Proposition 4, inequality (54), p. 21; proof p. 22

import Mathlib
import Definitions.Def_OptimalRLS_Minimax_Setting

open MeasureTheory ProbabilityTheory
open scoped InnerProductSpace RealInnerProductSpace

namespace OptimalRLS.Minimax

/-- **Proposition 4**, inequality (54), Caponnetto & De Vito (2007), p. 21. In the setting of §5.3
(as in `proposition_4_model`: `dim Y = d < +∞`, Hypothesis 1 with `κ`, `ν` with the spectral
decomposition (52) satisfying (17)), let `(vⱼ)` be an orthonormal basis of `Y`, `L = 4√(κ^c R)`, and
`f = T^{(c−1)/2} g`, `f′ = T^{(c−1)/2} g′` with `‖g‖² ≤ R` and `‖g′‖² ≤ R`. Then the Kullback–Leibler
information of `ρ_f` and `ρ_{f′}` satisfies
`K(ρ_f, ρ_{f′}) ≤ (16/(15 d L²)) ‖√T(f − f′)‖²_H`, where `‖√T h‖²_H = ∫ ‖h(x)‖² dν(x)` is `covForm ν h h`.
(The page's second hypothesis "‖g‖² ≤ R" is read as `‖g′‖² ≤ R`.) -/
theorem proposition_4_kl
    {X Y H : Type*} [TopologicalSpace X] [PolishSpace X] [MeasurableSpace X] [BorelSpace X]
    [NormedAddCommGroup Y] [InnerProductSpace ℝ Y] [CompleteSpace Y]
    [TopologicalSpace.SeparableSpace Y] [MeasurableSpace Y] [BorelSpace Y] [FiniteDimensional ℝ Y]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    [TopologicalSpace.SeparableSpace H] [MeasurableSpace H] [BorelSpace H] [RKHS ℝ H X Y]
    {ι : Type*} (κ : ℝ) (v : HilbertBasis ι ℝ Y) (h1 : Hyp1 H κ v)
    (R α β b c : ℝ) (hR : 0 < R) (hα : 0 < α) (hβ : 0 < β)
    (hb : 1 < b) (hc1 : 1 ≤ c) (hc2 : c ≤ 2)
    (ν : Measure X) [IsProbabilityMeasure ν] (e : ℕ → H) (t : ℕ → ℝ)
    (heig : IsEigenSystem ν e t) (hanti : Antitone t)
    (h17 : ∀ n : ℕ, α ≤ ((n : ℝ) + 1) ^ b * t n ∧ ((n : ℝ) + 1) ^ b * t n ≤ β)
    (vb : OrthonormalBasis (Fin (Module.finrank ℝ Y)) ℝ Y)
    (g g' : H) (hg : ‖g‖ ^ 2 ≤ R) (hg' : ‖g'‖ ^ 2 ≤ R) (f f' : H)
    (hf : f = Tpow e t ((c - 1) / 2) g) (hf' : f' = Tpow e t ((c - 1) / 2) g') :
    InformationTheory.klDiv (rhoF ν vb (Lconst κ c R) f) (rhoF ν vb (Lconst κ c R) f') ≤
      ENNReal.ofReal (16 / (15 * (Module.finrank ℝ Y : ℝ) * Lconst κ c R ^ 2) *
        covForm ν (f - f') (f - f')) := by sorry

end OptimalRLS.Minimax
