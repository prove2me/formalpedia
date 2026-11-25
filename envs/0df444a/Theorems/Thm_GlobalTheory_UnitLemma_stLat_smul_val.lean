-- Prove2me | Theorems.Thm_GlobalTheory_UnitLemma_stLat_smul_val
-- name    : GlobalTheory.UnitLemma.stLat_smul_val
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T04:29:15.643557+00:00
-- url     : https://prove2.me/theorems/21d969e1-8e95-5c96-bb2c-31a69af1949a
-- title:
--   Unit Lemma: st Lat smul val
-- statement:
--   The Unit Lemma construction uses the st Lat smul val property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ComapInlMemStLat.lean#L51-L52
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ComapInlMemStLat.lean#L51-L52

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
variable (O : Type) [CommRing O] (E : Type) [Field E] {A : Type} [CommRing A] [Algebra O A] [Algebra E A]

theorem GlobalTheory.UnitLemma.stLat_smul_val (g : A) (t : Aˣ) (L : stLat O E g) :
    ((t • L : stLat O E g) : Submodule O A) = mulLat O (t : A) L := by sorry
