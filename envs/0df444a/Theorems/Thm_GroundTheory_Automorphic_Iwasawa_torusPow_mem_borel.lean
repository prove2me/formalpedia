-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_Iwasawa_torusPow_mem_borel
-- name    : GroundTheory.Automorphic.Iwasawa.torusPow_mem_borel
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T13:18:33.882862+00:00
-- url     : https://prove2.me/theorems/9659d01d-79b4-4390-9c10-011f6a7d4b4f
-- title:
--   Iwasawa: torus Pow mem borel
-- statement:
--   The Iwasawa construction uses the torus Pow mem borel property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/Iwasawa.lean#L190-L191
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/Iwasawa.lean#L190-L191

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

theorem GroundTheory.Automorphic.Iwasawa.torusPow_mem_borel (l : Fin n → ℤ) : torusPow F n l ∈ borel F n := by sorry
