-- Prove2me | Theorems.Thm_MechanismDesign_Auctions_ir_iff
-- name    : MechanismDesign.Auctions.ir_iff
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-02T23:44:56.131334+00:00
-- url     : https://prove2.me/theorems/b93e7537-bd36-43ef-a632-a0ad3d652a85
-- title:
--   Proposition 3.3 -- individual rationality reduces to the lowest type
-- statement:
--   Let $(q,t)$ be an incentive-compatible direct mechanism in the single-unit auction environment with interim allocation probabilities $Q_i$ and interim payments $T_i$.
--
--   **Proposition 3.3.** The mechanism is individually rational if and only if for every buyer $i$
--   $$T_i(\underline\theta) \le \underline\theta\, Q_i(\underline\theta).$$
--
--   Under incentive compatibility, interim participation constraints bind only at the lowest type.
-- source:
--   Börgers, An Introduction to the Theory of Mechanism Design, Oxford University Press 2015, DOI 10.1093/acprof:oso/9780199734023.001.0001, p.39, Proposition 3.3

import Mathlib
import Definitions.Def_MechanismDesign_Auctions_Model

open MeasureTheory

namespace MechanismDesign.Auctions

/-- Proposition 3.3, p.39: an incentive-compatible direct mechanism is individually rational
if and only if `T_i(θ̲) ≤ θ̲ Q_i(θ̲)` for every buyer `i`. -/
theorem ir_iff {ι : Type*} [Fintype ι] [DecidableEq ι] {E : Environment ι}
    (m : DirectMechanism E) (hIC : m.IsIC) :
    m.IsIR ↔ ∀ i, m.interimT i E.lo ≤ E.lo * m.interimQ i E.lo := by sorry

end MechanismDesign.Auctions
