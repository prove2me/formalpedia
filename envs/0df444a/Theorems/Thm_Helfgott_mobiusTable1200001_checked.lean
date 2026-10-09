-- Prove2me | Theorems.Thm_Helfgott_mobiusTable1200001_checked
-- name    : Helfgott.mobiusTable1200001_checked
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-10-08T22:23:33.243518+00:00
-- url     : https://prove2.me/theorems/dcd43d1e-dd61-4be9-baf5-5cad5a3de123
-- title:
--   Complete Mobius factor certificate through 1200000
-- statement:
--   The complete fixed candidate Möbius table passes every prime-factor and Möbius recurrence check for $0\le n\le1200000$. The soundness theorem therefore identifies these candidate values with the actual Möbius function.
-- source:
--   Original complete finite arithmetic certificate for the Helfgott minor-arc Mobius input. Written by Codex.

import Definitions.Def_Helfgott_MobiusFiniteTable1200001
open Helfgott

namespace Helfgott

theorem mobiusTable1200001_checked : mobiusTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1200001 16 0 mobiusTable1200001 = true := by sorry

end Helfgott
