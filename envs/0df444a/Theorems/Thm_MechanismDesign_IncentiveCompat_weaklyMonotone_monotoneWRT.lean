-- Prove2me | Theorems.Thm_MechanismDesign_IncentiveCompat_weaklyMonotone_monotoneWRT
-- name    : MechanismDesign.IncentiveCompat.weaklyMonotone_monotoneWRT
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-03T02:12:44.632946+00:00
-- url     : https://prove2.me/theorems/f17eb599-387d-44ba-913a-043a4481f416
-- title:
--   Proposition 5.4 -- weak monotonicity implies monotonicity with respect to any complete transitive order
-- statement:
--   Let $R$ be a complete and transitive order of the set $A$ of alternatives, and let $\succ_R$ be the induced partial order on types (Definition 5.6). If a decision rule $q$ is weakly monotone, then it is monotone with respect to $R$:
--   $$\theta \succ_R \theta' \;\Longrightarrow\; q(\theta)\,R\,q(\theta').$$
--
--   The order $R$ is arbitrary; only the order $\succ_R$ on types changes with it.
-- source:
--   Börgers, An Introduction to the Theory of Mechanism Design, Oxford University Press 2015, DOI 10.1093/acprof:oso/9780199734023.001.0001, p.105, Proposition 5.4

import Mathlib
import Definitions.Def_MechanismDesign_IncentiveCompat_Model

namespace MechanismDesign.IncentiveCompat

/-- Proposition 5.4 (p.105): for a complete and transitive order `R` of `A`, a weakly monotone
decision rule is monotone with respect to `R`. -/
theorem weaklyMonotone_monotoneWRT {A Θ : Type*} [Nonempty Θ] (u : A → Θ → ℝ)
    (R : A → A → Prop) (hR : IsCompleteTransitive R) (q : Θ → A) (hq : WeaklyMonotone u q) :
    MonotoneWRT u R q := by sorry

end MechanismDesign.IncentiveCompat
