-- Prove2me | Theorems.Thm_GlobalTheory_UnitPairNorm_exists_unit_pair
-- name    : GlobalTheory.UnitPairNorm.exists_unit_pair
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T21:38:01.049419+00:00
-- url     : https://prove2.me/theorems/1605a9bf-2a43-4b8b-974a-07681197d4ac
-- title:
--   Unit Pair Norm: exists unit pair
-- statement:
--   The Unit Pair Norm construction uses the exists unit pair property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ExistsUnitNorm.lean#L33-L66
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ExistsUnitNorm.lean#L33-L66

import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_UnitLemmaGroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsUnitNorm
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.UnitPairNorm
open Module
variable {O E : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field E]
  [Algebra O E] [IsFractionRing O E]
variable {V : Type} [AddCommGroup V] [Module E V] [Module O V] [IsScalarTower O E V]

theorem GlobalTheory.UnitPairNorm.exists_unit_pair (h : V → V → E)
    (hsmul : ∀ (s : E) (x z : V), h (s • x) z = s * h x z)
    (W : Submodule E V) (L : Submodule O V) (hfg : L.FG)
    (hsp : Submodule.span E (L : Set V) = W)
    (hdual : ∀ y ∈ W, (y ∈ L ↔ ∀ z ∈ L, h y z ∈ (algebraMap O E).range))
    (hne : L ≠ ⊥) :
    ∃ x ∈ L, ∃ y ∈ L, ∃ a : Oˣ, h x y = algebraMap O E a := by sorry
