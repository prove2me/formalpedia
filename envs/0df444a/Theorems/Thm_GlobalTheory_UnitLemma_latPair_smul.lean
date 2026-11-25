-- Prove2me | Theorems.Thm_GlobalTheory_UnitLemma_latPair_smul
-- name    : GlobalTheory.UnitLemma.latPair_smul
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T04:29:17.320852+00:00
-- url     : https://prove2.me/theorems/f57571e1-b229-4e4b-a51e-ad6be984410b
-- title:
--   Unit Lemma: lat Pair smul
-- statement:
--   The Unit Lemma construction uses the lat Pair smul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ComapInlMemStLat.lean#L74-L76
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ComapInlMemStLat.lean#L74-L76

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_UnitLemmaGroup
import Definitions.Def_ReciprocityTheory_DualLattices_ExistsSmulMemOfMemSpan
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ComapInlMemStLat
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.UnitLemma
open Polynomial
variable (O : Type) [CommRing O] (E : Type) [Field E] {A₁ A₂ : Type} [CommRing A₁] [CommRing A₂]
  [Algebra O A₁] [Algebra O A₂] [Algebra E A₁] [Algebra E A₂]

theorem GlobalTheory.UnitLemma.latPair_smul (g₁ : A₁) (g₂ : A₂) (t : (A₁ × A₂)ˣ) (p : LatPair O E g₁ g₂) :
    t • p = ((Units.map (MonoidHom.fst A₁ A₂) t • p.1, Units.map (MonoidHom.snd A₁ A₂) t • p.2) :
      LatPair O E g₁ g₂) := by sorry
