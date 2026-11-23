-- Prove2me | Theorems.Thm_GlobalTheory_DivLin_baseChange_skew_iso
-- name    : GlobalTheory.DivLin.baseChange_skew_iso
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T15:00:59.169703+00:00
-- url     : https://prove2.me/theorems/d843a3be-f24d-46b7-ba6d-572a2f7b9dc4
-- title:
--   Div Lin: base Change skew iso
-- statement:
--   The Div Lin construction uses the base Change skew iso property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ScaledRestrictionEndomorphisms.lean#L91-L109
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ScaledRestrictionEndomorphisms.lean#L91-L109

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_ConjugateOrderData
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ScaledRestrictionEndomorphisms
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain TensorProduct GlobalTheory.CMVal GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations
open Classical
open GlobalTheory GlobalTheory.DivLin
variable {O : Type} [CommRing O] {H : Type} [AddCommGroup H] [Module O H] {I : Type} [Fintype I]
  (R : Type) [CommRing R] [Algebra O R]

theorem GlobalTheory.DivLin.baseChange_skew_iso (B : LinearMap.BilinForm O H) {M M' : Module.End O H}
    (hskew : ∀ x y, B (M x) y + B x (M y) = 0) (hiso : ∀ x y, B (M x) (M' y) = 0) (x y : R ⊗[O] H) :
    B.baseChange R (M.baseChange R x) y + B.baseChange R x (M.baseChange R y) = 0 ∧
      B.baseChange R (M.baseChange R x) (M'.baseChange R y) = 0 := by sorry
