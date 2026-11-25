-- Prove2me | Theorems.Thm_GlobalTheory_Mass_StabSplit_latIn_smul
-- name    : GlobalTheory.Mass.StabSplit.latIn_smul
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T03:31:58.966371+00:00
-- url     : https://prove2.me/theorems/d958d195-f47a-4e79-82d0-26ab1c8f00fd
-- title:
--   Stab Split: lat In smul
-- statement:
--   The Stab Split construction uses the lat In smul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/DefiniteUnitaryStabilizerSubspaceProd.lean#L77-L91
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/DefiniteUnitaryStabilizerSubspaceProd.lean#L77-L91

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ChartGen
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_DiscreteSeriesUnitary__MaxMass_96db7412d6455637
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_DefiniteUnitaryStabilizerSubspaceProd
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Matrix GlobalTheory.Mass Formalism.HermitianLatticesTheory
open scoped ENNReal Classical
open GlobalTheory GlobalTheory.Mass GlobalTheory.Mass.StabSplit
variable {K V : Type} [Field K] [StarRing K] [AddCommGroup V] [Module K V]
open NumberField Matrix
open scoped ENNReal Classical
variable {K V : Type} [Field K] [StarRing K] [AddCommGroup V] [Module K V]

theorem GlobalTheory.Mass.StabSplit.latIn_smul {R : Type} [CommRing R] [Algebra R K] [Module R V]
    [IsScalarTower R K V] (h : V →ₗ⋆[K] V →ₗ[K] K) (U : Submodule K V) (g : _root_.Formalism.HermitianLatticesTheory.isom h)
    (hg : g • U = U) (L : Submodule R V) :
    _root_.GlobalTheory.Mass.latIn U (g • L) =
      _root_.GlobalTheory.Mass.StabSplit.res h U g hg • _root_.GlobalTheory.Mass.latIn U L := by sorry
