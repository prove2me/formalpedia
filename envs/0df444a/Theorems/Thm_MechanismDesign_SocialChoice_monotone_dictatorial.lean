-- Prove2me | Theorems.Thm_MechanismDesign_SocialChoice_monotone_dictatorial
-- name    : MechanismDesign.SocialChoice.monotone_dictatorial
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-03T03:48:30.532738+00:00
-- url     : https://prove2.me/theorems/96a88e10-d380-46f7-b669-895840ad5d92
-- title:
--   Proposition 8.5 -- every monotone direct mechanism with full range over at least three alternatives is dictatorial
-- statement:
--   Let $I$ be a finite set of agents and $A$ a finite set of alternatives with at least three elements. Let $f:\mathcal R^N\to A$ be a direct mechanism on profiles of linear orders whose range is $A$. If $f$ is monotone, i.e.
--   $$f(R)=a\ \text{ and }\ \forall i\ \forall b\ \big(a\,R_i\,b\Rightarrow a\,R_i'\,b\big)\quad\Longrightarrow\quad f(R')=a,$$
--   then $f$ is dictatorial: there is an agent $i$ such that $f(R)\,R_i\,a$ for every profile $R$ and every $a\in A$.
--
--   This is the Muller–Satterthwaite theorem, the core of the book's proof of the Gibbard–Satterthwaite theorem (following Reny, 2001). Since dominant strategy incentive compatibility implies monotonicity (Proposition 8.2), it strengthens the necessity half of Proposition 8.1.
--
--   **Formalization Note** Monotonicity is the book's Definition 8.4 (arbitrary profile changes, per-agent lower-contour inclusion). The dictator $i$ is fixed before the profile is quantified. "The range of $f$ is $A$" is surjectivity of $f$ on all profiles of linear orders.
-- source:
--   Börgers, An Introduction to the Theory of Mechanism Design, Oxford University Press 2015, DOI 10.1093/acprof:oso/9780199734023.001.0001, p.146, Proposition 8.5

import Mathlib
import Definitions.Def_MechanismDesign_SocialChoice_Model

namespace MechanismDesign.SocialChoice

/-- **Proposition 8.5** (Börgers, p.146; Muller–Satterthwaite, in Reny's 2001 proof): suppose
that `A` has at least three elements and that the range of `f` is `A`. If `f` is monotone,
then it is dictatorial. -/
theorem monotone_dictatorial {ι A : Type*} [Fintype ι] [Fintype A]
    (hA : 3 ≤ Fintype.card A) (f : DirectMechanism ι A) (hrange : Function.Surjective f)
    (hf : IsMonotone f) : IsDictatorial f := by sorry

end MechanismDesign.SocialChoice
