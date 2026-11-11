-- Prove2me | Theorems.Thm_LimitsLifting_Approximation_proposition_4_14
-- name    : LimitsLifting.Approximation.proposition_4_14
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-11T04:38:56.05501+00:00
-- url     : https://prove2.me/theorems/35a57107-9b99-4b79-af08-e291c10a0992
-- title:
--   Proposition 4.14 — the rectangle of an input is a $\rho$-structured $R_{C,\alpha}$
-- statement:
--   Let $F$ be an unsatisfiable CNF over $[n]$ in which every variable occurs and no clause is tautological, and let $m\ge1$. For every coordinate $(C,\alpha)$ of the canonical cover, the rectangle associated with the input function $g=x_{(C,\alpha)}$ is
--   $$R_g=R_{C,\alpha},$$
--   and $R_{C,\alpha}$ is $\rho$-structured, where $\rho$ is the restriction that sets the variables of $C$ so as to falsify it and leaves every other coordinate free.
--
--   The proposition makes the leaves of every rectangle circuit structured, which is where the simulation of Lemma 4.10 ends with a falsified clause.
--
--   Differences from the source:
--   - generalization: positive n and m = n^Δ → every n ≥ 0 and m ≥ 1; reason: the formulas hold for every positive block length, including n = 0 where both input spaces and each nonempty canonical factor are singletons; all source instances are included.
--   - encoding: [m], [n] → Fin m, Fin n; reason: index shift, same instances.
-- source:
--   Gaia Carenini, Bruno Cavalar, Stefan Grosser, Jan Pich, Limits of Lifting, STOC 2027 submission #309 (October 2026), Proposition 4.14, printed p. 23 (PDF p. 24)

import Mathlib
import Definitions.Def_MultiplierAssoc206_Resolution_CNF
import Definitions.Def_LimitsLifting_Approximation_ApproxModel
import Definitions.Def_LimitsLifting_Approximation_CanonicalCover
import Definitions.Def_LimitsLifting_Approximation_RectangleScheme
open MultiplierAssoc206.Resolution

namespace LimitsLifting.Approximation

theorem proposition_4_14 {n m : ℕ} (hm : 1 ≤ m) (F : CNF (Fin n)) (hF : StandingCNF F)
    (c : Coord m F) :
    rectOf (inputFn c) = canonRect c ∧
      IsStructured (falsifyingRestriction c.1.1) (canonRect c).1 (canonRect c).2 := by sorry

end LimitsLifting.Approximation
