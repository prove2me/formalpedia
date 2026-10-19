-- Prove2me | Theorems.Thm_FutileDynamics_StaticOpt_proposition_13
-- name    : FutileDynamics.StaticOpt.proposition_13
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-19T06:50:31.09543+00:00
-- url     : https://prove2.me/theorems/cf6bc198-9e5a-4edb-b60e-86c61dd81897
-- title:
--   Proposition 13 (1–2), p. ec 21 — OPT(F,T) ≤ T·ū(F), OPT(δθ,T) = T·ū(δθ); ū the first-best benchmark (E-8) without IC (corrected)
-- statement:
--   Let $\bar u(F)$ be the first-best single-round benchmark: the largest expected principal utility of a single-round direct rule, without any incentive constraint, subject only to nonnegative expected agent utility under $F$. Then:
--
--   1. for every distribution $F\in\Delta(\Theta)$,
--   $$\mathrm{OPT}(F,T)\le T\cdot\bar u(F);$$
--   2. for every $\theta\in\Theta$,
--   $$\mathrm{OPT}(\delta_\theta,T)=T\cdot\bar u(\delta_\theta).$$
--
--   For a point mass, the known-distribution benchmark over $T$ rounds is $T$ times the first-best single-round value. This gives Proposition 1.
--
--   **Formalization Note** The page defines $\bar u$ (E-8) as a supremum over $S\in\mathcal S^{\times1}$ (IC mechanisms), but p. 22 describes it as the benchmark "when incentive compatibility constraints are dropped". The proof (pp. ec 23–24) uses a non-IC $S$ in part 1 and a supremum over all outcome distributions in part 2. The Lean $\bar u$ ranges over all jointly measurable direct rules (corrected). Part 3 is not used and is left out. Assumed throughout: $0<T$, $\Theta$ standard Borel and nonempty, and the model conventions.
-- source:
--   Balseiro, Kim & Russo, On the futility of dynamics in robust mechanism design, SSRN 3449698 (version of October 5, 2020), p. ec 21, Proposition 13 (parts 1–2), (E-8); proof pp. ec 23–24

import Mathlib
import Definitions.Def_FutileDynamics_StaticOpt_Model

namespace FutileDynamics.StaticOpt

open MeasureTheory

/-- **Proposition 13**, parts 1–2 (p. ec 21), with the first-best benchmark `ū` of (E-8) **corrected** to
range over all single-round direct rules, without incentive compatibility (the page writes `S ∈ S^{×1}`;
p. 22 and the proof, pp. ec 23–24, drop IC): (1) `OPT(F, T) ≤ T · ū(F)` for every distribution `F`;
(2) `OPT(δ_θ, T) = T · ū(δ_θ)` for every `θ`. -/
theorem proposition_13 {Θ Ω : Type} [MeasurableSpace Θ] [MeasurableSpace Ω] [StandardBorelSpace Θ] [Nonempty Θ]
    (G : Game Θ Ω) (T : ℕ) (hT : 0 < T) :
    (∀ F : Measure Θ, IsProbabilityMeasure F → OPT G F T ≤ T * ubar G F) ∧
    ∀ θ : Θ, OPT G (Measure.dirac θ) T = T * ubar G (Measure.dirac θ) := by sorry

end FutileDynamics.StaticOpt
