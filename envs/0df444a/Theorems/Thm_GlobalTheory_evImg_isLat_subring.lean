-- Prove2me | Theorems.Thm_GlobalTheory_evImg_isLat_subring
-- name    : GlobalTheory.evImg_isLat_subring
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T22:20:04.739227+00:00
-- url     : https://prove2.me/theorems/c469a23b-433b-46d3-8524-c6e1c3cfe370
-- title:
--   Global Theory: ev Img is Lat subring
-- statement:
--   The Global Theory construction uses the ev Img is Lat subring property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/EvImgIsLatSubring.lean#L20-L106
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/EvImgIsLatSubring.lean#L20-L106

import Mathlib
import Definitions.Def_ReciprocityTheory_DualLattices_EvLatStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_EvImgIsLatSubring
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open TensorProduct IsLocalRing Matrix ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Be2
open GlobalTheory
open TensorProduct IsLocalRing Matrix

theorem GlobalTheory.evImg_isLat_subring :
  (∀ {R₀ : Type} [CommRing R₀] {p : ℕ} [Fact p.Prime] {g : ℕ} {B : _root_.ReciprocityTheory.PGsh.BX R₀} {Tw : _root_.ReciprocityTheory.PGsh.ATowerL R₀ p} {Dt : _root_.ReciprocityTheory.PGsh.DualTower Tw} [Algebra ℤ_[p] (Tw.O : Type)] {Oe : Type} [CommRing Oe] [Algebra ℤ_[p] Oe] {σ : Oe ≃ₐ[ℤ_[p]] Oe} {cp : (Tw.O : Type)} (D : _root_.ReciprocityTheory.PGsh.Be2.Dat p g B Tw Dt Oe σ cp), _root_.ReciprocityTheory.PGsh.Be2.EvLatStatement D) := by sorry
