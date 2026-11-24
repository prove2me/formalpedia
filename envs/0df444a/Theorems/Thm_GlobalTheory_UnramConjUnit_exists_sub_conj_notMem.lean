-- Prove2me | Theorems.Thm_GlobalTheory_UnramConjUnit_exists_sub_conj_notMem
-- name    : GlobalTheory.UnramConjUnit.exists_sub_conj_notMem
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T21:46:47.567492+00:00
-- url     : https://prove2.me/theorems/966eb85c-aea1-4483-b1f8-0a608629f66b
-- title:
--   Unram Conj Unit: exists sub conj not Mem
-- statement:
--   The Unram Conj Unit construction uses the exists sub conj not Mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/ExistsSubConjNotMem.lean#L31-L106
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/ExistsSubConjNotMem.lean#L31-L106

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_DisjointSpanPerpLat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_ExistsSubConjNotMem
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.IndefiniteRowSideFullHecke.UnitaryLatticeOrthogonal GlobalTheory.SelfDualLatticeCompare
open GlobalTheory GlobalTheory.UnramConjUnit
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {σ : E →ₐ[F] E}
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {σ : E →ₐ[F] E}

theorem GlobalTheory.UnramConjUnit.exists_sub_conj_notMem (h : _root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.IsCMExt F E σ)
    (v : HeightOneSpectrum (𝓞 F)) (hv : _root_.GlobalTheory.IndefiniteRowSideFullHecke.UnitaryLatticeOrthogonal.UnramAt F E v) :
    ∃ (t d : 𝓞 E) (s : 𝓞 F), (d : E) = (t : E) - σ t ∧
      algebraMap F E (s : F) = (d : E) * d ∧ s ∉ v.asIdeal := by sorry
