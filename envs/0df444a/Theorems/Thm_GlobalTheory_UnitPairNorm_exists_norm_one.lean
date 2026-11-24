-- Prove2me | Theorems.Thm_GlobalTheory_UnitPairNorm_exists_norm_one
-- name    : GlobalTheory.UnitPairNorm.exists_norm_one
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T21:37:55.703485+00:00
-- url     : https://prove2.me/theorems/5e4061fc-0379-4a3e-aa6f-8ba74995af68
-- title:
--   Unit Pair Norm: exists norm one
-- statement:
--   The Unit Pair Norm construction uses the exists norm one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ExistsUnitNorm.lean#L117-L134
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ExistsUnitNorm.lean#L117-L134

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

theorem GlobalTheory.UnitPairNorm.exists_norm_one (c : E ≃+* E)
    (hnorm : ∀ u : Oˣ, c (algebraMap O E u) = algebraMap O E u →
      ∃ z : Oˣ, algebraMap O E u = algebraMap O E z * c (algebraMap O E z))
    (h : V → V → E)
    (hsmul : ∀ (s : E) (x z : V), h (s • x) z = s * h x z)
    (hsym : ∀ x y : V, h y x = c (h x y))
    (L : Submodule O V) (e : V) (he : e ∈ L) (u : Oˣ) (hu : h e e = algebraMap O E u) :
    ∃ e' ∈ L, h e' e' = 1 := by sorry
