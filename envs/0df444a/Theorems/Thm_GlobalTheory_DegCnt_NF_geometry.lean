-- Prove2me | Theorems.Thm_GlobalTheory_DegCnt_NF_geometry
-- name    : GlobalTheory.DegCnt.NF.geometry
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T04:44:59.46789+00:00
-- url     : https://prove2.me/theorems/23b8422e-625d-4f10-9ffc-d7eb9cda569a
-- title:
--   NF: geometry
-- statement:
--   The NF construction uses the geometry property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/HermFramePairNormalFormGeometrySummary.lean#L920-L987
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/HermFramePairNormalFormGeometrySummary.lean#L920-L987

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_FlagPairDefinitePartLattice
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ChartGen
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_DiscreteSeriesUnitary__MaxMass_96db7412d6455637
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_NormalFormDualOrthogonalLast
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_ExistsHasLeadingCoeffOfMemSpanBelow
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_SameBlockAppend
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_HermFramePairNormalFormGeometrySummary
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Formalism.HermitianLatticeCounting.S6 GlobalTheory.HermLat GlobalTheory.DegCnt
open scoped Pointwise ENNReal Classical
open Formalism.HermitianLatticeCounting.P
noncomputable section
open GlobalTheory GlobalTheory.DegCnt
open NumberField
open scoped Pointwise ENNReal Classical
variable {K V : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
  {H : _root_.Formalism.HermitianLatticeCounting.S6.HermSpace K V} {r : ℕ} (N : _root_.GlobalTheory.DegCnt.NF H r)

theorem GlobalTheory.DegCnt.NF.geometry : ∀ (K V : Type) [Field K]
    [NumberField K] [StarRing K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (H : _root_.Formalism.HermitianLatticeCounting.S6.HermSpace K V), _root_.Formalism.HermitianLatticesTheory.IsCMUnram K →
    ∀ (r : ℕ) (N : _root_.GlobalTheory.DegCnt.NF H r),
      _root_.Formalism.HermitianLatticeCounting.S6.NFFull N.F N.F' N.j
          N.j_le N.c ∧
        _root_.Formalism.HermitianLatticeCounting.S6.IsLift N.F N.F' N.Wt ∧
        IsCompl N.Wt N.Pi ∧
        Module.finrank K N.Wt + 2 * r + 1 = Module.finrank K V ∧
        N.Wn =
          N.Wt ⊔ Submodule.span K {N.F.z} ∧
        _root_.GlobalTheory.HermLat.uPerp N.F N.F' =
          N.Wn ⊔ _root_.Formalism.HermitianLatticeCounting.S6.II N.F N.F' ∧
        _root_.GlobalTheory.HermLat.wSp N.F N.F' =
          N.Wt ⊔ _root_.Formalism.HermitianLatticeCounting.S6.II N.F N.F' ∧
        _root_.GlobalTheory.HermLat.wSp N.F' N.F =
          _root_.GlobalTheory.HermLat.wSp N.F N.F' ∧
        _root_.GlobalTheory.Mass.PD
          (_root_.GlobalTheory.Mass.hRes H.B.flip N.Wt) ∧
        1 ≤ N.T ∧
        N.nD N.j ≠ 0 ∧
        N.Pi =
          _root_.Formalism.HermitianLatticeCounting.S6.V0 N.F N.F' ⊔ N.Ist := by sorry
