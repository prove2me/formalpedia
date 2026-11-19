-- Prove2me | Theorems.Thm_JonesUnknot_jonesA_reidemeister_invariant
-- name    : JonesUnknot.jonesA_reidemeister_invariant
-- status  : Open
-- author  : @LG
-- created : 2026-11-17T00:32:57.393107+00:00
-- url     : https://prove2.me/theorems/d476cc3c-a430-4b65-9b6f-b19d6654ef16
-- title:
--   The normalized Jones polynomial is a Reidemeister invariant
-- statement:
--   If two PD codes $D$ and $D'$ are related by a sequence of Reidemeister moves, then their normalized brackets agree: $f_D=f_{D'}$.
--
--   This is Kauffman's theorem that the normalized Kauffman bracket is invariant under the three Reidemeister moves, so it descends to an invariant of the knot — the Jones polynomial. It makes $f_D=1$ a property of the knot rather than of the chosen diagram, and underlies the well-definedness of the goal.
--
--   **Formalization Note.** Stated for all diagrams using the platform's `PD.ReidemeisterEquiv`; no planarity or single-component hypothesis is needed for invariance.
-- source:
--   Epoch AI FrontierMath, The Jones Unknot Conjecture, https://epoch.ai/frontiermath/open-problems/jones-unknot (Prompt and Diagram format sections). ; L. H. Kauffman, State models and the Jones polynomial, Topology 26 (1987), 395-407 (bracket invariance).

import Mathlib
import Definitions.Def_ManolescuPiccirillo_PD
import Definitions.Def_ManolescuPiccirillo_Kirby
import Definitions.Def_ManolescuPiccirillo_Lee1
import Definitions.Def_JonesUnknot_planar
import Definitions.Def_JonesUnknot_jones
import Definitions.Def_JonesUnknot_genus
open ManolescuPiccirillo JonesUnknot

namespace JonesUnknot
theorem jonesA_reidemeister_invariant (D D' : PD) (h : D.ReidemeisterEquiv D') :
    jonesA D = jonesA D' := by sorry
end JonesUnknot
