-- Prove2me | Theorems.Thm_MechanismDesign_SocialChoice_gibbard_satterthwaite
-- name    : MechanismDesign.SocialChoice.gibbard_satterthwaite
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-03T03:48:26.772195+00:00
-- url     : https://prove2.me/theorems/517a6133-54f5-4bc5-8baf-593adeaf8d9a
-- title:
--   Proposition 8.1 -- the Gibbard–Satterthwaite theorem
-- statement:
--   Let $I$ be a finite set of agents and $A$ a finite set of alternatives with at least three elements, and let $f:\mathcal R^N\to A$ be a direct mechanism on profiles of linear orders whose range is $A$. Then
--   $$f \text{ is dominant strategy incentive-compatible}\iff f \text{ is dictatorial},$$
--   where dictatorial means that some agent $i$ satisfies $f(R)\,R_i\,a$ for every profile $R$ and every $a\in A$.
--
--   This is the Gibbard (1973)–Satterthwaite (1975) theorem: with an unrestricted domain of strict preferences and at least three attainable alternatives, strategy-proofness forces a dictatorship. With two alternatives the conclusion fails (majority voting is strategy-proof), which is why $|A|\ge 3$ is essential.
--
--   **Formalization Note** Both directions of the book's "if and only if" are stated. The range assumption is surjectivity of $f$ on all profiles of linear orders.
-- source:
--   Börgers, An Introduction to the Theory of Mechanism Design, Oxford University Press 2015, DOI 10.1093/acprof:oso/9780199734023.001.0001, p.143, Proposition 8.1

import Mathlib
import Definitions.Def_MechanismDesign_SocialChoice_Model

namespace MechanismDesign.SocialChoice

/-- **Proposition 8.1** (Gibbard–Satterthwaite; Börgers, p.143): suppose that `A` has at least
three elements and that the range of a direct mechanism `f` is `A`. Then `f` is dominant
strategy incentive-compatible if and only if it is dictatorial. -/
theorem gibbard_satterthwaite {ι A : Type*} [Fintype ι] [DecidableEq ι] [Fintype A]
    (hA : 3 ≤ Fintype.card A) (f : DirectMechanism ι A) (hrange : Function.Surjective f) :
    IsDSIC f ↔ IsDictatorial f := by sorry

end MechanismDesign.SocialChoice
