-- Prove2me | Theorems.Thm_GlobalTheory_PDivGroup_SemiHom_rigToExt_rig
-- name    : GlobalTheory.PDivGroup.SemiHom.rigToExt_rig
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T02:50:14.875961+00:00
-- url     : https://prove2.me/theorems/3707813a-6a28-5f72-be40-eec4685ac3a6
-- title:
--   Semi Hom: rig To Ext rig
-- statement:
--   The Semi Hom construction uses the rig To Ext rig property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/ToBaseChangePtsBijective.lean#L375-L377
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/ToBaseChangePtsBijective.lean#L375-L377

import Mathlib
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Divisors__EqZeroOfCobOneEqZero_fe26957659067348
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_ToBaseChangePtsBijective
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open TensorProduct Coalgebra Bialgebra WithConv CategoryTheory
open GlobalTheory
open GlobalTheory.PDivGroup
open PDiv
variable {p : ℕ} {O O' O'' : Type} [CommRing O] [CommRing O'] [CommRing O'']
open GlobalTheory.PDivGroup.SemiHom
variable {σ : O →+* O'} {τ : O' →+* O''} {G H : PDivGroup p O} {G' H' : PDivGroup p O'}
  {G'' : PDivGroup p O''}
variable (s : SemiHom σ G' G)

theorem GlobalTheory.PDivGroup.SemiHom.rigToExt_rig (x : G.RigExt) : G'.rigToExt (s.rig x) = s.vecExt (G.rigToExt x) := by sorry
