-- Prove2me | Theorems.Thm_MechanismDesign_DominantExamples_pg_epir_iff
-- name    : MechanismDesign.DominantExamples.pg_epir_iff
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-03T01:30:27.519176+00:00
-- url     : https://prove2.me/theorems/dc14dcc0-9674-406d-a5af-9eb3b52fbc35
-- title:
--   Proposition 4.6 — ex post IR of public good mechanisms binds at the lowest type
-- statement:
--   Let $(q, t_1, \dots, t_N)$ be a dominant strategy incentive-compatible deterministic direct public good mechanism on $\Theta = [\underline\theta,\bar\theta]^I$. It is ex post individually rational if and only if for every agent $i$ and every $\theta_{-i} \in \Theta_{-i}$
--   $$t_i(\underline\theta,\theta_{-i}) \le \underline\theta\, q(\underline\theta,\theta_{-i}).$$
--
--   As in the auction case, only the participation constraint of the lowest type needs to be checked.
-- source:
--   Börgers, An Introduction to the Theory of Mechanism Design, Oxford University Press 2015, DOI 10.1093/acprof:oso/9780199734023.001.0001, p.87, Proposition 4.6

import Mathlib
import Definitions.Def_MechanismDesign_DominantExamples_PublicGood

namespace MechanismDesign.DominantExamples

/-- Proposition 4.6, p.87. A dominant strategy incentive-compatible direct public good
mechanism is ex post individually rational if and only if for every agent `i` and every
`θ_{-i} ∈ Θ_{-i}`: `t_i(θ̲, θ_{-i}) ≤ θ̲ q(θ̲, θ_{-i})`. -/
theorem pg_epir_iff {ι : Type*} [Fintype ι] [DecidableEq ι] {E : PublicGoodSetting}
    (M : PublicGoodMechanism E ι) (hM : M.IsDSIC) :
    M.IsEPIR ↔ ∀ i, ∀ θ ∈ E.typeSpace ι,
      M.t i (Function.update θ i E.lo) ≤ E.lo * M.q (Function.update θ i E.lo) := by sorry

end MechanismDesign.DominantExamples
