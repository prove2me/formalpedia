-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_Iwasawa_unipotent_le_borel
-- name    : GroundTheory.Automorphic.Iwasawa.unipotent_le_borel
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T17:41:35.715173+00:00
-- url     : https://prove2.me/theorems/c2d127c3-0d2e-4639-a18e-df5f136b10b5
-- title:
--   Iwasawa: unipotent le borel
-- statement:
--   The Iwasawa construction uses the unipotent le borel property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/Iwasawa.lean#L86-L86
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/Iwasawa.lean#L86-L86

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_GLnLattice
import Definitions.Def_GroundTheory_AutomorphicForms_Iwasawa
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GroundTheory GroundTheory.Automorphic
open ValuativeRel Matrix Filter
open scoped Pointwise
open GroundTheory.Automorphic.Iwasawa
open GLnLocal
variable (F : Type*) [Field F] (n : ℕ)

theorem GroundTheory.Automorphic.Iwasawa.unipotent_le_borel : unipotent F n ≤ borel F n := by sorry
