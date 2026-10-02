-- Prove2me | Theorems.Thm_LearnStability_ConvexSCO_theorem8_stable_aerm
-- name    : LearnStability.ConvexSCO.theorem8_stable_aerm
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T18:16:21.235049+00:00
-- url     : https://prove2.me/theorems/d5d217db-7554-48fc-8cc9-5d7e690918e4
-- title:
--   Theorem 8: a stable AERM is consistent and generalizes
-- statement:
--   Work in the General Learning Setting with a nonempty hypothesis class $\mathcal H$, an objective with $|f(h;z)|\le C$ for all $h,z$, and a distribution $D$. Suppose the learning rule $A$ is an AERM with rate $\varepsilon_{\mathrm{erm}}(m)$ under $D$, and is either average-RO stable under $D$ or uniform-RO stable, with rate $\varepsilon_{\mathrm{stable}}(m)$. Then $A$ is consistent and generalizes under $D$, for every $m\ge1$, with rates
--   $$\varepsilon_{\mathrm{cons}}(m)\le\varepsilon_{\mathrm{stable}}(m)+\varepsilon_{\mathrm{erm}}(m),\qquad \varepsilon_{\mathrm{gen}}(m)\le\varepsilon_{\mathrm{stable}}(m)+2\varepsilon_{\mathrm{erm}}(m)+\frac{2C}{\sqrt m}.$$
--
--   Stability together with approximate empirical minimization is thus sufficient for learning, with no uniform convergence involved. In this mission it is the step that converts Eq. (6) into the expected excess-risk bound of Theorem 2.
--
--   **Formalization Note** The paper's loss bound $B$ is written $C$. Measurability conventions of the series are hypotheses: each $f(h;\cdot)$ is measurable, the rule is measurable ($(S,z)\mapsto f(A(S);z)$ jointly measurable), and $S\mapsto\inf_hF_S(h)$ is measurable. Rates are arbitrary real sequences; no monotonicity is needed.
-- source:
--   Shalev-Shwartz, Shamir, Srebro and Sridharan, Learnability, Stability and Uniform Convergence, JMLR 11 (2010), p. 2649, Theorem 8

import Mathlib
import Definitions.Def_LearnStability_ConvexSCO_Setting

open MeasureTheory

namespace LearnStability.ConvexSCO

/-- Theorem 8 (p. 2649), in the General Learning Setting with a nonempty hypothesis type `H`,
an objective bounded by `C` (the paper's standing bound `B`), a measurable rule and a
measurable minimal empirical risk. If `A` is an AERM with rate `ε_erm` under `D` and is
average-RO stable under `D` or uniform-RO stable with rate `ε_stable`, then `A` is consistent
under `D` with rate `ε_stable + ε_erm` and generalizes under `D` with rate
`ε_stable + 2 ε_erm + 2C/√m`. -/
theorem theorem8_stable_aerm {Z H : Type*} [MeasurableSpace Z] [Nonempty H]
    (f : H → Z → ℝ) (C : ℝ) (hC : ∀ h z, |f h z| ≤ C) (hf : ∀ h, Measurable (f h))
    (herm : ErmValueMeasurable f) (A : (m : ℕ) → (Fin m → Z) → H)
    (hA : IsMeasurableRule f A) (D : Measure Z) [IsProbabilityMeasure D]
    (εerm εstable : ℕ → ℝ) (haerm : IsAERMUnder f A D εerm)
    (hstable : AverageROStableUnder f A D εstable ∨ UniformROStable f A εstable) :
    IsConsistentUnder f A D (fun m => εstable m + εerm m) ∧
      GeneralizesUnder f A D
        (fun m => εstable m + 2 * εerm m + 2 * C / Real.sqrt m) := by sorry

end LearnStability.ConvexSCO
