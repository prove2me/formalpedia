-- Prove2me | Theorems.Thm_LeGallBrownianMap_corollary_7_3
-- name    : LeGallBrownianMap.corollary_7_3
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T02:38:34.441325+00:00
-- url     : https://prove2.me/theorems/59ec34db-a40c-49dd-87fb-8d8b6b91712b
-- title:
--   Corollary 7.3 — $D^*(U,V)$ has the law of $\Delta$
-- statement:
--   Let $e$ be a normalized Brownian excursion, $Z$ Brownian labels given $e$, and $U,V$ independent random variables uniform on $[0,1]$ such that $(U,V)$ is independent of $(e,Z)$. Then
--
--   $$
--   D^*(U,V)\overset{(d)}{=}D^*(s_*,U)=Z_U+\Delta\overset{(d)}{=}\Delta .
--   $$
--
--   That is: $D^*(U,V)$ and $D^*(s_*,U)$ have the same law, $D^*(s_*,U)=Z_U+\Delta$ almost surely, and $Z_U+\Delta$ has the law of $\Delta$. In the Brownian map the distance between two uniform points has the law of the distance from a uniform point to $x_*$; this is used for triangulations in §8.
--
--   **Formalization Note** Equality in law is `IdentDistrib`, which includes the a.e.-measurability of both sides.
--
--   Differences from the source:
--   - encoding: a normalized Brownian excursion e and labels Z with the conditional law of §2.4 → e = OAI.FKCRT.standardExcursion B (norm of a 3-dimensional Brownian bridge) for three independent Brownian motions B, and Z with IsBrownianLabels (conditional characteristic functions), on any probability space; reason: the Bessel bridge has the law of the normalized excursion and the characteristic-function identity is the conditional Gaussian law; quantifying over all realizations pins the law
--   - reading: the identity D∗(s∗, U) = Z_U + ∆ between random variables → almost surely; reason: an identity between random variables
-- source:
--   Le Gall, Uniqueness and universality of the Brownian map, arXiv:1105.4842v2, Corollary 7.3, p.61

import Mathlib
import Definitions.Def_FKCRT
import Definitions.Def_LeGallBrownianMap_IsBrownianLabels
import Definitions.Def_LeGallBrownianMap_dStar
import Definitions.Def_LeGallBrownianMap_sStar
import Definitions.Def_LeGallBrownianMap_labelDelta

open MeasureTheory ProbabilityTheory OAI.FKCRT
open scoped NNReal

namespace LeGallBrownianMap

/-- Le Gall, *Uniqueness and universality of the Brownian map*, arXiv:1105.4842v2,
Corollary 7.3, p.61: "Let U and V be two independent random variables uniformly distributed over
[0, 1] and such that the pair (U, V) is independent of (e, Z). Then,
D∗(U, V) =(d) D∗(s∗, U) = Z_U + ∆ =(d) ∆."

For a realization of `(e, Z)` and `U, V` independent uniform on `[0,1]` with `(U, V)` independent of
`(e, Z)`:
1. `D∗(U, V)` and `D∗(s∗, U)` have the same law;
2. `D∗(s∗, U) = Z_U + ∆` almost surely;
3. `Z_U + ∆` and `∆` have the same law.

**Formalization Note.** `(e, Z)` is realized as in `LeGallBrownianMap.theorem_1_1`
(`e = standardExcursion B`). Equality in law is `ProbabilityTheory.IdentDistrib`, which also
asserts that both sides are a.e.-measurable (so the laws are not junk zero measures). `s∗` is
`sStar Z` (a minimizer of `Z`, a.s. unique) and `∆ = −min Z` is `labelDelta Z`. Independence of
`(U, V)` from `(e, Z)` is with the product σ-algebras on paths. -/
theorem corollary_7_3 {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (B : Fin 3 → ℝ≥0 → Ω → ℝ) (hB : ∀ i, IsBrownianReal (B i) P)
    (hind : iIndepFun (fun i ω t => B i t ω) P)
    (Z : unitInterval → Ω → ℝ) (hZ : IsBrownianLabels (fun ω => standardExcursion B ω) Z P)
    (U V : Ω → unitInterval) (hU : Measurable U) (hV : Measurable V)
    (hUlaw : P.map U = volume) (hVlaw : P.map V = volume) (hUV : IndepFun U V P)
    (hUVeZ : IndepFun (fun ω => (U ω, V ω))
      (fun ω => (standardExcursion B ω, fun t => Z t ω)) P) :
    IdentDistrib
        (fun ω => dStar (standardExcursion B ω) (fun t => Z t ω) (U ω) (V ω))
        (fun ω => dStar (standardExcursion B ω) (fun t => Z t ω)
          (sStar (fun t => Z t ω)) (U ω)) P P ∧
      (∀ᵐ ω ∂P, dStar (standardExcursion B ω) (fun t => Z t ω) (sStar (fun t => Z t ω)) (U ω) =
        Z (U ω) ω + labelDelta (fun t => Z t ω)) ∧
      IdentDistrib (fun ω => Z (U ω) ω + labelDelta (fun t => Z t ω))
        (fun ω => labelDelta (fun t => Z t ω)) P P := by sorry

end LeGallBrownianMap
