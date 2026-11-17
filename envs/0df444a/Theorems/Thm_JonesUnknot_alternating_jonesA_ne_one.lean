-- Prove2me | Theorems.Thm_JonesUnknot_alternating_jonesA_ne_one
-- name    : JonesUnknot.alternating_jonesA_ne_one
-- status  : Open
-- author  : @Lucas
-- created : 2026-11-17T00:34:18.1252+00:00
-- url     : https://prove2.me/theorems/215999be-3fdb-4b8f-8014-c89e76289b1c
-- title:
--   Reduced alternating knots have nontrivial Jones polynomial
-- statement:
--   A reduced alternating planar knot diagram $D$ with at least one crossing has nontrivial normalized Jones polynomial: $f_D\neq 1$.
--
--   This is the alternating case of the Jones unknot conjecture, a theorem of Kauffman, Murasugi and Thistlethwaite: for a reduced alternating diagram the span of the Jones polynomial equals the crossing number, so a nontrivial alternating knot cannot have Jones polynomial $1$. It rules out alternating knots as counterexamples and is a key partial result toward the goal.
--
--   **Formalization Note.** The span theorem implies the stated nontriviality; `Reduced` and `Alternating` are the combinatorial predicates from the genus layer.
-- source:
--   Epoch AI FrontierMath, The Jones Unknot Conjecture, https://epoch.ai/frontiermath/open-problems/jones-unknot (Prompt and Diagram format sections). ; K. Murasugi, Jones polynomials and classical conjectures in knot theory, Topology 26 (1987), 187-194 ; M. B. Thistlethwaite, A spanning tree expansion of the Jones polynomial, Topology 26 (1987), 297-309.

import Mathlib
import Definitions.Def_ManolescuPiccirillo_PD
import Definitions.Def_ManolescuPiccirillo_Kirby
import Definitions.Def_ManolescuPiccirillo_Lee1
import Definitions.Def_JonesUnknot_planar
import Definitions.Def_JonesUnknot_jones
import Definitions.Def_JonesUnknot_genus
open ManolescuPiccirillo JonesUnknot

namespace JonesUnknot
theorem alternating_jonesA_ne_one (D : PD) (hK : D.IsKnot) (hP : Planar D)
    (hR : Reduced D) (hA : Alternating D) (hn : 0 < D.numCrossings) :
    jonesA D ≠ 1 := by sorry
end JonesUnknot
