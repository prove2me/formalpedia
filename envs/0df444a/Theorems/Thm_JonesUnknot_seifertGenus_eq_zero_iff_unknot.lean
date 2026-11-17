-- Prove2me | Theorems.Thm_JonesUnknot_seifertGenus_eq_zero_iff_unknot
-- name    : JonesUnknot.seifertGenus_eq_zero_iff_unknot
-- status  : Open
-- author  : @Lucas
-- created : 2026-11-17T00:33:39.924342+00:00
-- url     : https://prove2.me/theorems/a2273dbe-be3a-4dec-9d17-de0f145334d0
-- title:
--   Seifert genus detects the unknot
-- statement:
--   For a planar single-component knot diagram $D$, the Seifert genus is zero if and only if $D$ is Reidemeister-equivalent to the crossingless diagram (the unknot):
--   $$g(D)=0\ \Longleftrightarrow\ D\sim\varnothing.$$
--
--   This is the statement that the Seifert genus detects the unknot: a knot bounds a genus-zero orientable surface (a disk) exactly when it is trivial. It connects the combinatorial genus used in the goal to genuine knottedness, and is the classical counterpart of the fact that knot Floer homology detects the genus (Ozsváth–Szabó). It justifies reading $g(D)>0$ in the goal as "$D$ is not the unknot".
--
--   **Formalization Note.** `⟨[]⟩` is the empty PD code, which the platform treats as the unknot (`numComponents = 1`).
-- source:
--   Epoch AI FrontierMath, The Jones Unknot Conjecture, https://epoch.ai/frontiermath/open-problems/jones-unknot (Prompt and Diagram format sections). ; P. Ozsváth, Z. Szabó, Holomorphic disks and genus bounds, Geom. Topol. 8 (2004), 311-334.

import Mathlib
import Definitions.Def_ManolescuPiccirillo_PD
import Definitions.Def_ManolescuPiccirillo_Kirby
import Definitions.Def_ManolescuPiccirillo_Lee1
import Definitions.Def_JonesUnknot_planar
import Definitions.Def_JonesUnknot_jones
import Definitions.Def_JonesUnknot_genus
open ManolescuPiccirillo JonesUnknot

namespace JonesUnknot
theorem seifertGenus_eq_zero_iff_unknot (D : PD) (hK : D.IsKnot) (hP : Planar D) :
    seifertGenus D = 0 ↔ D.ReidemeisterEquiv ⟨[]⟩ := by sorry
end JonesUnknot
