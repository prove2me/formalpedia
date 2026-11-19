-- Prove2me | Theorems.Thm_JonesUnknot_jones_unknot_conjecture_false
-- name    : JonesUnknot.jones_unknot_conjecture_false
-- status  : Open
-- author  : @LG
-- created : 2026-11-17T00:35:33.775838+00:00
-- url     : https://prove2.me/theorems/b8142f5f-6cba-4f68-a1b1-63921569d3db
-- title:
--   The Jones unknot conjecture is false
-- statement:
--   The Jones unknot conjecture is false: there is a nontrivial knot whose normalized Jones polynomial is $1$.
--
--   Concretely, there exists a planar diagram (PD) code $D$ such that
--   1. $D$ is a valid single-component knot diagram (`IsKnot`) and is planar (`Planar`);
--   2. its normalized Jones polynomial is $1$, i.e. $f_D(A)=(-A^3)^{-w(D)}\langle D\rangle=1$ (equivalently $V_K(t)=1$);
--   3. its Seifert genus is positive, $g(D)>0$, so the knot is genuinely knotted and not the unknot.
--
--   This is the bare negation of the conjecture that the unknot is the only knot with Jones polynomial $1$, and the goal of the FrontierMath open problem. The statement leaves the crossing number unfixed.
--
--   **Formalization Note.** $f_D=1$ is used in place of $V_K=1$ because for a knot the exponents of $f_D$ are multiples of $4$ and $f_D(A)=V_K(A^{-4})$; nontriviality is the knot invariant `seifertGenus` (minimum over the Reidemeister class), not the canonical genus of $D$.
-- source:
--   Epoch AI FrontierMath, The Jones Unknot Conjecture, https://epoch.ai/frontiermath/open-problems/jones-unknot (Prompt and Diagram format sections).

import Mathlib
import Definitions.Def_ManolescuPiccirillo_PD
import Definitions.Def_ManolescuPiccirillo_Kirby
import Definitions.Def_ManolescuPiccirillo_Lee1
import Definitions.Def_JonesUnknot_planar
import Definitions.Def_JonesUnknot_jones
import Definitions.Def_JonesUnknot_genus
open ManolescuPiccirillo JonesUnknot

namespace JonesUnknot
theorem jones_unknot_conjecture_false :
    ∃ D : PD, D.IsKnot ∧ Planar D ∧ jonesA D = 1 ∧ 0 < seifertGenus D := by sorry
end JonesUnknot
