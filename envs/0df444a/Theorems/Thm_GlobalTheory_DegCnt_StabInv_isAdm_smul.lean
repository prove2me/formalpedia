-- Prove2me | Theorems.Thm_GlobalTheory_DegCnt_StabInv_isAdm_smul
-- name    : GlobalTheory.DegCnt.StabInv.isAdm_smul
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T03:58:48.510831+00:00
-- url     : https://prove2.me/theorems/139be29a-b99e-521c-810f-dbc837883b36
-- title:
--   Stab Inv: is Adm smul
-- statement:
--   The Stab Inv construction uses the is Adm smul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/CommonUnipotentStabiliserPreservesTermsAndDatum.lean#L137-L154
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/CommonUnipotentStabiliserPreservesTermsAndDatum.lean#L137-L154

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_FlagPairDefinitePartLattice
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ChartGen
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_DiscreteSeriesUnitary__MaxMass_96db7412d6455637
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_NormalFormDualOrthogonalLast
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_CommonUnipotentStabiliserPreservesTermsAndDatum
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
open GlobalTheory GlobalTheory.DegCnt GlobalTheory.DegCnt.StabInv
variable {K V : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
  [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] {H : HermSpace K V} {r : ℕ}

theorem GlobalTheory.DegCnt.StabInv.isAdm_smul {F F' : FlagD H r} {s : V ≃ₗ[K] V} (h : Keeps F s) (h' : Keeps F' s)
    {Λ : Submodule (𝓞 K) V} {g : 𝓞 K} (hΛ : IsAdm F F' Λ g) : IsAdm F F' (s • Λ) g := by sorry
