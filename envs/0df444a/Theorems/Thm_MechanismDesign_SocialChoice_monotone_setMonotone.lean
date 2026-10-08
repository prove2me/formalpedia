-- Prove2me | Theorems.Thm_MechanismDesign_SocialChoice_monotone_setMonotone
-- name    : MechanismDesign.SocialChoice.monotone_setMonotone
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-03T03:48:06.629201+00:00
-- url     : https://prove2.me/theorems/5968d2de-8a79-46d1-ac89-58e923a41a6b
-- title:
--   Proposition 8.3 -- monotonicity implies set-monotonicity
-- statement:
--   Let $f:\mathcal R^N\to A$ be a direct mechanism on profiles of linear orders over a finite set $A$ of alternatives. If $f$ is monotone (Definition 8.4), then $f$ is set-monotone: whenever $f(R)\in B$ for some $B\subseteq A$ and, for every agent $i$,
--   $$a\,R_i'\,a'\iff a\,R_i\,a'\qquad\text{for all } a,a'\in A \text{ with } a\notin B \text{ or } a'\notin B,$$
--   then $f(R')\in B$.
--
--   Set-monotonicity says that reshuffling agents' rankings inside a set $B$ cannot move the outcome out of $B$; it is used with $B=\{a,b\}$ throughout the proof of Proposition 8.5.
-- source:
--   Börgers, An Introduction to the Theory of Mechanism Design, Oxford University Press 2015, DOI 10.1093/acprof:oso/9780199734023.001.0001, p.145, Proposition 8.3 (Definition 8.5)

import Mathlib
import Definitions.Def_MechanismDesign_SocialChoice_Model

namespace MechanismDesign.SocialChoice

/-- **Proposition 8.3** (Börgers, p.145): if `f` is monotone, then `f` is set-monotone. -/
theorem monotone_setMonotone {ι A : Type*} [Fintype ι] [Fintype A]
    (f : DirectMechanism ι A) (hf : IsMonotone f) : IsSetMonotone f := by sorry

end MechanismDesign.SocialChoice
