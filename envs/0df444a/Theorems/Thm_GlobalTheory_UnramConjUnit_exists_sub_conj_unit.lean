-- Prove2me | Theorems.Thm_GlobalTheory_UnramConjUnit_exists_sub_conj_unit
-- name    : GlobalTheory.UnramConjUnit.exists_sub_conj_unit
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T19:37:45.96684+00:00
-- url     : https://prove2.me/theorems/e11abfa9-344c-4533-bb96-84442fb79c93
-- title:
--   Unram Conj Unit: exists sub conj unit
-- statement:
--   The Unram Conj Unit construction uses the exists sub conj unit property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/ExistsSubConjNotMem.lean#L113-L154
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/ExistsSubConjNotMem.lean#L113-L154

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

theorem GlobalTheory.UnramConjUnit.exists_sub_conj_unit : ∀ (F E : Type) [Field F] [NumberField F] [Field E]
    [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), _root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.IsCMExt F E σ →
    ∀ v : HeightOneSpectrum (𝓞 F), _root_.GlobalTheory.IndefiniteRowSideFullHecke.UnitaryLatticeOrthogonal.UnramAt F E v →
    ∃ θ ∈ _root_.GlobalTheory.IndefiniteRowSideFullHecke.UnitaryLatticeOrthogonal.OEv F E v, ∃ b ∈ _root_.GlobalTheory.IndefiniteRowSideFullHecke.UnitaryLatticeOrthogonal.OEv F E v,
      (θ - _root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v) σ θ) * b = 1 := by sorry
