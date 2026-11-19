-- Prove2me | Theorems.Thm_JonesUnknot_counterexample_100_crossings
-- name    : JonesUnknot.counterexample_100_crossings
-- status  : Open
-- author  : @LG
-- created : 2026-11-17T00:34:54.086949+00:00
-- url     : https://prove2.me/theorems/5247daf0-bfd6-4171-8de4-981c3f6ab2b4
-- title:
--   A trivial-Jones nontrivial knot on at most 100 crossings
-- statement:
--   There exists a planar single-component knot diagram $D$ with at most $100$ crossings whose normalized Jones polynomial is $1$ and whose Seifert genus is positive:
--   $$\exists\,D,\ \mathrm{IsKnot}(D)\wedge\mathrm{Planar}(D)\wedge n(D)\le 100\wedge f_D=1\wedge g(D)>0.$$
--
--   This is the concrete form of the FrontierMath counterexample: a nontrivial knot with trivial Jones polynomial presented by a diagram within the benchmark's $100$-crossing limit. It implies the goal. The benchmark also requires the diagram to be reduced (no simplifying Reidemeister I/II move); this is without loss of generality, since reduction preserves the knot and its Jones polynomial and only lowers the crossing number.
--
--   **Formalization Note.** The reducedness requirement is omitted from the formal statement because it is a normalization: a qualifying diagram exists with $\le 100$ crossings iff a reduced one does.
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
theorem counterexample_100_crossings :
    ∃ D : PD, D.IsKnot ∧ Planar D ∧ D.numCrossings ≤ 100 ∧ jonesA D = 1 ∧ 0 < seifertGenus D := by sorry
end JonesUnknot
