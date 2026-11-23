-- Prove2me | Theorems.Thm_GlobalTheory_HermLineZeros_exists_conj_ne
-- name    : GlobalTheory.HermLineZeros.exists_conj_ne
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T16:03:25.93682+00:00
-- url     : https://prove2.me/theorems/798cdeaf-ae8d-4f2d-bd48-d536219cb5c5
-- title:
--   Herm Line Zeros: exists conj ne
-- statement:
--   The Herm Line Zeros construction uses the exists conj ne property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/HermitianFormFiniteZerosOnLineCmExt.lean#L53-L64
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/HermitianFormFiniteZerosOnLineCmExt.lean#L53-L64

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
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {σ : E →ₐ[F] E}
open scoped TensorProduct
open NumberField IsDedekindDomain MeasureTheory Topology
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {σ : E →ₐ[F] E}

theorem GlobalTheory.HermLineZeros.exists_conj_ne (h : _root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.IsCMExt F E σ) : ∃ d, σ d ≠ d := by sorry
