-- Prove2me | Theorems.Thm_GoldieRenewal_Implicit_key_renewal_limit
-- name    : GoldieRenewal.Implicit.key_renewal_limit
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T17:11:37.856966+00:00
-- url     : https://prove2.me/theorems/b630d11e-4cab-4710-be63-2b029df22e41
-- title:
--   Proof of Theorem 2.3, Case 1, p. 145 — ř(t) → (1/m)∫_ℝ ğ₁ as t → ∞
-- statement:
--   Let $M$ satisfy the conditions of Lemma 2.2 with $M\ge0$ a.s., let $R$ be independent of $M$, and assume (2.8). With $r$, $g_1$ as in (9.3), (3.5) and $m = E|M|^\kappa\log|M|$,
--   $$
--   \check r(t)\to\frac1m\int_{\mathbb R}\check g_1,\qquad t\to\infty .
--   $$
--
--   Together with Lemma 9.3 and the identity $\int_{\mathbb R}\check g_1 = \int_{\mathbb R}g_1 = \int_0^\infty(P(R>u)-P(MR>u))u^{\kappa-1}du$, this gives (2.10) with the constant (2.12).
--
--   **Formalization Note** This is the conclusion, in the setting of Case 1, of applying the two-sided key renewal theorem to (9.8); it is not a general key renewal theorem. $\check g_1\in L^1(\mathbb R)$ under (2.8), so $\int_{\mathbb R}\check g_1$ is a genuine integral.
-- source:
--   Goldie, Implicit renewal theory and tails of solutions of random equations, Ann. Appl. Probab. 1(1):126–166 (1991), DOI 10.1214/aoap/1177005985, §9, proof of Theorem 2.3, Case 1, unnumbered display after (9.8), p. 145

import Mathlib
import Definitions.Def_GoldieRenewal_Implicit_CramerConditions
import Definitions.Def_GoldieRenewal_Implicit_DRi
import Definitions.Def_GoldieRenewal_Implicit_TailConstants
open MeasureTheory ProbabilityTheory Filter Topology

namespace GoldieRenewal.Implicit

/-- **Key renewal limit of Case 1** (Goldie 1991, Ann. Appl. Probab. 1(1), §9, proof of
Theorem 2.3, Case 1, unnumbered display after (9.8), p. 145): `ř(t) → (1/m) ∫_ℝ ğ₁` as `t → ∞`.

Setting: `M` satisfies the conditions of Lemma 2.2, `M ≥ 0` a.s., `R` is independent of `M`, and
(2.8) holds; `r(t) := e^{κt} P(R > e^t)` (9.3), `g₁(t) := e^{κt}(P(R > e^t) − P(MR > e^t))` (3.5),
`m := E|M|^κ log|M|` (2.7).

**Formalization Note** This is the conclusion of applying the key renewal theorem to (9.8) in this
setting, not a general key renewal theorem. `ğ₁ ∈ L¹(ℝ)` under (2.8) (Young's inequality: `g₁ ∈ L¹`
by the substitution `t = e^u`, and the smoothing kernel has integral `1`), so `∫_ℝ ğ₁` is the
paper's value. -/
theorem key_renewal_limit {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (M R : Ω → ℝ) (hM : Measurable M) (hR : Measurable R) (κ : ℝ)
    (hC : CramerConditions κ (P.map M)) (hind : IndepFun R M P)
    (hM_nonneg : ∀ᵐ ω ∂P, 0 ≤ M ω) (h28 : TailCondPlus P M R κ) :
    Tendsto (smooth (rFun P R κ)) atTop
      (𝓝 ((cramerMean κ (P.map M))⁻¹ * ∫ t, smooth (gOne P M R κ) t)) := by sorry

end GoldieRenewal.Implicit
