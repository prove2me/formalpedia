-- Prove2me | Theorems.Thm_GlobalTheory_HermLineZeros_hform_expand
-- name    : GlobalTheory.HermLineZeros.hform_expand
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T07:36:30.495864+00:00
-- url     : https://prove2.me/theorems/0b7f3ea4-26d2-4200-8499-a1ca8e64e4e0
-- title:
--   Herm Line Zeros: hform expand
-- statement:
--   The Herm Line Zeros construction uses the hform expand property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/HermitianFormFiniteZerosOnLineCmExt.lean#L16-L25
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/HermitianFormFiniteZerosOnLineCmExt.lean#L16-L25

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_GlobalSchurBounds_GeneralLinearActions_GenusMassVolumes
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_HermitianFormFiniteZerosOnLineCmExt
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped TensorProduct
open NumberField IsDedekindDomain MeasureTheory Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory GlobalTheory.HermLineZeros
variable {A : Type} [CommRing A] {M : ℕ}
open scoped TensorProduct
open NumberField IsDedekindDomain MeasureTheory Topology
variable {A : Type} [CommRing A] {M : ℕ}

theorem GlobalTheory.HermLineZeros.hform_expand (s : A →+* A) (J : Matrix (Fin M) (Fin M) A)
    (x y : Fin M → A) (c : A) :
    _root_.Formalism.UG.hform s J (x + c • y) (x + c • y) =
      _root_.Formalism.UG.hform s J x x + c * _root_.Formalism.UG.hform s J x y + s c * _root_.Formalism.UG.hform s J y x
        + s c * c * _root_.Formalism.UG.hform s J y y := by sorry
