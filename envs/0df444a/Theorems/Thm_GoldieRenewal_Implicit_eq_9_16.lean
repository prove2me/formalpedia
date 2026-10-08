-- Prove2me | Theorems.Thm_GoldieRenewal_Implicit_eq_9_16
-- name    : GoldieRenewal.Implicit.eq_9_16
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T17:11:36.63998+00:00
-- url     : https://prove2.me/theorems/75ec8db2-ad97-4199-b8db-4c8532005ffd
-- title:
--   (9.16), p. 148 — in Case 2b (M ≤ 0 a.s.), ∫₀^∞ |P(R > t) − P(MM′R > t)| t^{κ−1} dt < ∞
-- statement:
--   Let $M$ satisfy the conditions of Lemma 2.2 with $M\le0$ a.s., let $M'$ have the law of $M$, and let $R, M, M'$ be independent. If (2.8) and (2.9) hold, then
--   $$
--   \int_0^\infty |P(R>t)-P(MM'R>t)|\,t^{\kappa-1}\,dt<\infty . \tag{9.16}
--   $$
--
--   This reduces Case 2b to Case 1: the product $MM'$ is nonnegative and satisfies the conditions of Lemma 2.2 with the same $\kappa$, and (9.16) is condition (2.8) for it.
--
--   **Formalization Note** The conclusion is condition (2.8) with $MM'$ in place of $M$. The copy $M'$ lives on the same probability space as $R$ and $M$ (the paper's common probability space, p. 144).
-- source:
--   Goldie, Implicit renewal theory and tails of solutions of random equations, Ann. Appl. Probab. 1(1):126–166 (1991), DOI 10.1214/aoap/1177005985, §9, proof of Theorem 2.3, Case 2b, (9.16), p. 148

import Mathlib
import Definitions.Def_GoldieRenewal_Implicit_CramerConditions
import Definitions.Def_GoldieRenewal_Implicit_TailConstants
open MeasureTheory ProbabilityTheory

namespace GoldieRenewal.Implicit

/-- **(9.16)** (Goldie 1991, Ann. Appl. Probab. 1(1), §9, proof of Theorem 2.3, Case 2b, p. 148).
Suppose `M` satisfies the conditions of Lemma 2.2 and `M ≤ 0` a.s., `M′` has the law of `M`, and
`R, M, M′` are independent. If (2.8) and (2.9) hold, then
`∫₀^∞ |P(R > t) − P(MM′R > t)| t^{κ−1} dt < ∞`.

**Formalization Note** The conclusion is (2.8) for the multiplier `MM′` in place of `M`
(`TailCondPlus P (M·M′) R κ`, integrability of the signed integrand on `(0, ∞)`). The copy `M′` is
assumed on the given probability space (the paper's "common probability space", p. 144):
the statement quantifies over every space carrying such `R, M, M′`. -/
theorem eq_9_16 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (M M' R : Ω → ℝ) (hM : Measurable M) (hM' : Measurable M') (hR : Measurable R) (κ : ℝ)
    (hC : CramerConditions κ (P.map M)) (hident : IdentDistrib M' M P P)
    (hind : iIndepFun (fun i : Fin 3 => (![R, M, M'] : Fin 3 → Ω → ℝ) i) P)
    (hM_nonpos : ∀ᵐ ω ∂P, M ω ≤ 0)
    (h28 : TailCondPlus P M R κ) (h29 : TailCondMinus P M R κ) :
    TailCondPlus P (fun ω => M ω * M' ω) R κ := by sorry

end GoldieRenewal.Implicit
