-- Prove2me | Theorems.Thm_HuangN13_N13MumfordFullKummerTwoSurjective_twoSurjective
-- name    : HuangN13.N13MumfordFullKummerTwoSurjective.twoSurjective
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-10-30T10:24:59.37187+00:00
-- url     : https://prove2.me/theorems/483aed73-4f8b-4a36-bc55-2c8bf1f49315
-- title:
--   Multiplication by two is surjective on the N13 Picard group
-- statement:
--   The actual fake-Kummer value of every Picard class is zero. The original full-gauge equivalence turns this into a full-gauge witness, from which the retained constructor supplies a chosen half and its doubling identity. Thus every class is twice another class.
-- source:
--   Xiang Huang, Apache-2.0. Original source: https://github.com/xiangyazi24/FLT/blob/51bbb4f191ad0d3753b87123635c100a638ae580/FLT/Assumptions/MazurProof/N13MumfordFullKummerTwoSurjective.lean; exact unit7 lines7830-7835, source-command SHA-256 300312855e686682d058a43d5d0b90e75e28a2f54e2dea56af048ad0c69278f6. Original-file line mapping is not asserted.

import Mathlib
import Definitions.Def_MazurN13_L4

set_option autoImplicit false

theorem HuangN13.N13MumfordFullKummerTwoSurjective.twoSurjective :
    MazurProof.N13TwoAdicEndgame.TwoSurjective MazurProof.N13MumfordFullKummerTwoSurjective.G := by sorry
