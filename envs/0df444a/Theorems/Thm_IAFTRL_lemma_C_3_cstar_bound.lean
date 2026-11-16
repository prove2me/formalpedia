-- Prove2me | Theorems.Thm_IAFTRL_lemma_C_3_cstar_bound
-- name    : IAFTRL.lemma_C_3_cstar_bound
-- status  : Proved
-- author  : @Canzhe Zhao
-- created : 2026-11-15T08:05:40.602389+00:00
-- url     : https://prove2.me/theorems/442b9c6b-1cba-498b-9c20-d13dc430302c
-- title:
--   Lemma C.3 (second claim) — $c^*(\mathcal A,\theta)\le 2d/\Delta_{\min}$
-- statement:
--   Let $\mathcal A=\{a_1,\dots,a_K\}$ be a finite action set in the Euclidean unit ball of $\mathbb R^d$ ($d\ge1$) that spans $\mathbb R^d$. Let $\theta\in\mathbb R^d$ have a unique minimizing action $a^*$, write $\Delta(a)=(a-a^*)^\top\theta$ for the loss gap, and let $0<\Delta_0\le\Delta(a)$ for every $a\ne a^*$. Then the information-acquisition complexity (1.2),
--   $$
--   c^*(\mathcal A,\theta)=\inf_{n\in\mathbb R_{\ge0}^{\mathcal A}}\Big\{\sum_a n_a\Delta(a)\;:\;H_n=\sum_a n_a aa^\top\succ0,\ \|a\|^2_{H_n^{-1}}\le\tfrac{\Delta(a)^2}{2}\ \forall a\ne a^*\Big\},
--   $$
--   satisfies
--   $$
--   c^*(\mathcal A,\theta)\le\frac{2d}{\Delta_0}.
--   $$
--
--   At $\Delta_0=\Delta_{\min}$ this is the bound $c^*\le 2d\Delta_{\min}^{-1}$: the instance-dependent leading constant of IA-FTRL is never worse than the classical $d/\Delta_{\min}$ rate.
--
--   **Formalization Note** This is the second conjunct of `IAFTRL.lemma_C_3`, with the same hypotheses; $c^*(\mathcal A,\theta)$ is `BanditAlgorithm.linearBanditAllocationValue arms (−θ)` (rewards convention, so its gap at $-\theta$ is the loss gap $\Delta$).
-- source:
--   Zhao–Tan, Best-of-Both-Worlds FTRL for Linear Bandits, arXiv:2611.01299, Lemma C.3, p.60 (second sentence: "Also c* ≤ 2dΔ_min^{-1}")

import Mathlib
import Definitions.Def_LinearBanditProtocol
import Definitions.Def_IAFTRL_IsActionSet
import Definitions.Def_IAFTRL_IsUniqueMin

namespace IAFTRL

open Matrix

/-- **Lemma C.3, second claim (`c* ≤ 2d/Δ_min`).** Zhao–Tan, *Best-of-Both-Worlds FTRL for Linear
Bandits*, arXiv:2611.01299, Lemma C.3, p.60: "Also `c* ≤ 2dΔ_min^{−1}`."

Same setting as `IAFTRL.lemma_C_3`: `𝒜 = {a_1, …, a_K}` a finite action set in the unit ball of `ℝ^d`
spanning `ℝ^d`, `θ` with a unique minimizing action `a* = a_{jstar}`, and `0 < Δ₀ ≤ Δ(a)` for all
`a ≠ a*`. Then `c*(𝒜, θ) ≤ 2d/Δ₀`.

**Formalization Note.** The second conjunct of `IAFTRL.lemma_C_3`, with the same hypotheses and
conventions (`c*` is `BanditAlgorithm.linearBanditAllocationValue arms (−θ)`). -/
theorem lemma_C_3_cstar_bound {d K : ℕ} (hd : 1 ≤ d) (arms : Fin K → Fin d → ℝ) (hA : IsActionSet arms)
    (θ : Fin d → ℝ) (jstar : Fin K) (hu : IsUniqueMin arms θ jstar) (Δ₀ : ℝ) (hΔ₀ : 0 < Δ₀)
    (hΔ : ∀ j, j ≠ jstar → Δ₀ ≤ (arms j - arms jstar) ⬝ᵥ θ) :
    BanditAlgorithm.linearBanditAllocationValue arms (-θ) ≤ 2 * (d : ℝ) / Δ₀ := by sorry

end IAFTRL
