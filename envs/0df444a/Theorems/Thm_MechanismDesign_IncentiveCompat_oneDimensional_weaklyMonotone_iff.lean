-- Prove2me | Theorems.Thm_MechanismDesign_IncentiveCompat_oneDimensional_weaklyMonotone_iff
-- name    : MechanismDesign.IncentiveCompat.oneDimensional_weaklyMonotone_iff
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-03T02:12:30.888134+00:00
-- url     : https://prove2.me/theorems/737f2fdb-1611-4b7e-9dd3-86792cf782bb
-- title:
--   Proposition 5.5 -- on one-dimensional type spaces, weak monotonicity iff monotonicity with respect to R
-- statement:
--   Let $R$ be a complete and transitive order of $A$ such that the type set $\Theta$ is one-dimensional with respect to $R$: any two distinct types $\theta \ne \theta'$ satisfy $\theta \succ_R \theta'$ or $\theta' \succ_R \theta$. Then a decision rule $q$ is weakly monotone if and only if it is monotone with respect to $R$, that is,
--   $$\theta \succ_R \theta' \;\Longrightarrow\; q(\theta)\,R\,q(\theta').$$
--
--   On one-dimensional domains weak monotonicity thus reduces to the familiar requirement that higher types receive higher alternatives.
-- source:
--   Börgers, An Introduction to the Theory of Mechanism Design, Oxford University Press 2015, DOI 10.1093/acprof:oso/9780199734023.001.0001, p.106, Proposition 5.5

import Mathlib
import Definitions.Def_MechanismDesign_IncentiveCompat_Model

namespace MechanismDesign.IncentiveCompat

/-- Proposition 5.5 (p.106): if `Θ` is one-dimensional with respect to a complete and transitive
order `R` of `A`, a decision rule is weakly monotone if and only if it is monotone with respect
to `R`. -/
theorem oneDimensional_weaklyMonotone_iff {A Θ : Type*} [Nonempty Θ] (u : A → Θ → ℝ)
    (R : A → A → Prop) (hR : IsCompleteTransitive R) (h1 : OneDimensional u R) (q : Θ → A) :
    WeaklyMonotone u q ↔ MonotoneWRT u R q := by sorry

end MechanismDesign.IncentiveCompat
