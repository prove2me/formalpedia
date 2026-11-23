-- Prove2me | Theorems.Thm_GlobalTheory_IndefiniteRowSideFullHecke_SelfDualLatticeActions_sigR_mem
-- name    : GlobalTheory.IndefiniteRowSideFullHecke.SelfDualLatticeActions.sigR_mem
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T05:58:47.098621+00:00
-- url     : https://prove2.me/theorems/c71eae8d-652a-44c3-a4b4-983133c8acb7
-- title:
--   Self Dual Lattice Actions: sig R mem
-- statement:
--   The Self Dual Lattice Actions construction uses the sig R mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/GlobalSignature/SelfDualLatticeActions.lean#L180-L187
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/GlobalSignature/SelfDualLatticeActions.lean#L180-L187

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_GlobalSchurBounds_GeneralLinearActions_GenusMassVolumes
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_GlobalSignature_SelfDualLatticeActions
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped TensorProduct
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.IndefiniteRowSideFullHecke.SelfDualLatticeActions
variable {F : Type} [Field F] [NumberField F] {E : Type} [Field E] [Algebra F E]
  (v : HeightOneSpectrum (𝓞 F)) (σ : E →ₐ[F] E)
open scoped TensorProduct
open NumberField IsDedekindDomain
variable {F : Type} [Field F] [NumberField F] {E : Type} [Field E] [Algebra F E]
  (v : HeightOneSpectrum (𝓞 F)) (σ : E →ₐ[F] E)

theorem GlobalTheory.IndefiniteRowSideFullHecke.SelfDualLatticeActions.sigR_mem {z : _root_.GlobalTheory.IndefiniteRowSideFullHecke.SelfDualLatticeActions.Ev E v}
    (hz : z ∈ _root_.GlobalTheory.IndefiniteRowSideFullHecke.SelfDualLatticeActions.OEv E v) :
    _root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v) σ z ∈ _root_.GlobalTheory.IndefiniteRowSideFullHecke.SelfDualLatticeActions.OEv E v := by sorry
