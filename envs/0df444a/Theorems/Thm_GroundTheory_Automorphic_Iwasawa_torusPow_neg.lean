-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_Iwasawa_torusPow_neg
-- name    : GroundTheory.Automorphic.Iwasawa.torusPow_neg
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T13:23:01.165867+00:00
-- url     : https://prove2.me/theorems/d1a4ae57-bc8d-49ef-9b7c-79558bb8b4f1
-- title:
--   Iwasawa: torus Pow neg
-- statement:
--   The Iwasawa construction uses the torus Pow neg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/Iwasawa.lean#L376-L380
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/Iwasawa.lean#L376-L380

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
variable [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]

theorem GroundTheory.Automorphic.Iwasawa.torusPow_neg (l : Fin n → ℤ) : torusPow F n (-l) = (torusPow F n l)⁻¹ := by sorry
