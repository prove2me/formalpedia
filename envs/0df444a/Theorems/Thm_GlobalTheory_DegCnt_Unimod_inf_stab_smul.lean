-- Prove2me | Theorems.Thm_GlobalTheory_DegCnt_Unimod_inf_stab_smul
-- name    : GlobalTheory.DegCnt.Unimod.inf_stab_smul
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T04:45:24.684597+00:00
-- url     : https://prove2.me/theorems/4dd2d7e3-7173-4f1c-817b-fe22ed92b5b3
-- title:
--   Unimod: inf stab smul
-- statement:
--   The Unimod construction uses the inf stab smul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/RelIndexNeZero.lean#L153-L167
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/RelIndexNeZero.lean#L153-L167

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_FlagPairDefinitePartLattice
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ChartGen
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_DiscreteSeriesUnitary__MaxMass_96db7412d6455637
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_NormalFormDualOrthogonalLast
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_InvVolMulPosLeConj
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_ExistsIntSmulLe
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_ImportsBisTer
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_RelIndexNeZero
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
open GlobalTheory GlobalTheory.DegCnt GlobalTheory.DegCnt.Unimod
variable {K V : Type} [Field K] [NumberField K] [AddCommGroup V] [Module K V]
  [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]

theorem GlobalTheory.DegCnt.Unimod.inf_stab_smul {Γ X : Type} [Group Γ] [MulAction Γ X] (G : Subgroup Γ) {s : Γ} (hs : s ∈ G) (x : X) :
    G ⊓ MulAction.stabilizer Γ (s • x) = MulAut.conj s • (G ⊓ MulAction.stabilizer Γ x) := by sorry
