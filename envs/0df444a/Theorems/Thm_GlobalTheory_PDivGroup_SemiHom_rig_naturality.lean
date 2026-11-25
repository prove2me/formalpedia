-- Prove2me | Theorems.Thm_GlobalTheory_PDivGroup_SemiHom_rig_naturality
-- name    : GlobalTheory.PDivGroup.SemiHom.rig_naturality
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T12:16:10.561348+00:00
-- url     : https://prove2.me/theorems/9fd9b072-37b8-5f5f-a0af-725305e93de0
-- title:
--   Semi Hom: rig naturality
-- statement:
--   The Semi Hom construction uses the rig naturality property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/ToBaseChangePtsBijective.lean#L416-L420
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/ToBaseChangePtsBijective.lean#L416-L420

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
variable [Fact p.Prime]

theorem GlobalTheory.PDivGroup.SemiHom.rig_naturality (s' : SemiHom σ H' H) (f : G ⟶ H) (f' : G' ⟶ H')
    (h : ∀ n a, s.app n (f.app n a) = f'.app n (s'.app n a)) (x : H.RigExt) :
    s.rig (rigExtMap f x) = rigExtMap f' (s'.rig x) := by sorry
