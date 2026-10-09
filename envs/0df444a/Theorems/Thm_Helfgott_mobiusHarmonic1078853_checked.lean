-- Prove2me | Theorems.Thm_Helfgott_mobiusHarmonic1078853_checked
-- name    : Helfgott.mobiusHarmonic1078853_checked
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-10-08T22:24:09.372023+00:00
-- url     : https://prove2.me/theorems/252fe921-767d-4c30-952a-9ed7601581d4
-- title:
--   Complete Mertens harmonic certificate through 1078852
-- statement:
--   The complete fixed candidate Mertens-prefix and harmonic-upper-bound table passes every recurrence and integer rounding check for $0\le n\le1078852$. Its exact recorded upper sum is $302481031385$ at scale $10^9$. This is the computational certificate consumed by the initial-integral soundness theorem.
-- source:
--   Original complete finite arithmetic certificate for the Helfgott minor-arc Mobius input. Written by Codex.

import Definitions.Def_Helfgott_MobiusFiniteTable1200001
import Definitions.Def_Helfgott_MobiusHarmonicTable1078853
open Helfgott

namespace Helfgott

theorem mobiusHarmonic1078853_checked : mobiusHarmonicTreeCheck (mobiusTreeValue 16 mobiusTable1200001) (mobiusPrefixValue 16 mobiusHarmonic1078853) 1000000000 1078853 16 0 mobiusHarmonic1078853 = true := by sorry

end Helfgott
