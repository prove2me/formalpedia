-- Prove2me | Theorems.Thm_GlobalTheory_SatakeWeyl_unimodFin
-- name    : GlobalTheory.SatakeWeyl.unimodFin
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T19:49:14.680507+00:00
-- url     : https://prove2.me/theorems/43b93315-fcc5-450e-9f5c-0602bc28264c
-- title:
--   Satake Weyl: unimod Fin
-- statement:
--   The Satake Weyl construction uses the unimod Fin property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/FiniteIndexLeftRightCosetSumsEq.lean#L18-L36
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/FiniteIndexLeftRightCosetSumsEq.lean#L18-L36

import Mathlib
import Definitions.Def_Formalism_SatakeDualWeyl_KpqSubgroupCompact
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_AntiJMulApply
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_FiniteIndexLeftRightCosetSumsEq
import Theorems.Thm_Formalism_UG_Final_KpqSubgroupCompact

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.UG GlobalTheory.SatakeWeyl
open GlobalTheory GlobalTheory.SatakeWeyl

theorem GlobalTheory.SatakeWeyl.unimodFin : UnimodFin := by sorry
