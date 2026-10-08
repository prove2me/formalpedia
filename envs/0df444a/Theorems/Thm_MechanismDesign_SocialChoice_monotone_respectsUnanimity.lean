-- Prove2me | Theorems.Thm_MechanismDesign_SocialChoice_monotone_respectsUnanimity
-- name    : MechanismDesign.SocialChoice.monotone_respectsUnanimity
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-03T03:48:06.905416+00:00
-- url     : https://prove2.me/theorems/a0f1323f-fd64-4912-abff-cc42749bc022
-- title:
--   Proposition 8.4 -- a monotone mechanism with full range respects unanimity
-- statement:
--   Let $f:\mathcal R^N\to A$ be a direct mechanism on profiles of linear orders over a finite set $A$. If $f$ is monotone (Definition 8.4) and the range of $f$ is $A$, then $f$ respects unanimity: for every profile $R$ and alternative $a$,
--   $$a\,R_i\,b\ \text{ for all } i\in I,\ b\in A\quad\Longrightarrow\quad f(R)=a.$$
--
--   Unanimity is the anchor of the proof of Proposition 8.5: it pins down the outcome at the profiles where the argument starts and ends.
--
--   **Formalization Note** "The range of $f$ is $A$" is surjectivity of $f$ on the full domain $\mathcal R^N$.
-- source:
--   Börgers, An Introduction to the Theory of Mechanism Design, Oxford University Press 2015, DOI 10.1093/acprof:oso/9780199734023.001.0001, p.145, Proposition 8.4 (Definition 8.6)

import Mathlib
import Definitions.Def_MechanismDesign_SocialChoice_Model

namespace MechanismDesign.SocialChoice

/-- **Proposition 8.4** (Börgers, p.145): if `f` is monotone and the range of `f` is `A`, then
`f` respects unanimity. -/
theorem monotone_respectsUnanimity {ι A : Type*} [Fintype ι] [Fintype A]
    (f : DirectMechanism ι A) (hf : IsMonotone f) (hrange : Function.Surjective f) :
    RespectsUnanimity f := by sorry

end MechanismDesign.SocialChoice
