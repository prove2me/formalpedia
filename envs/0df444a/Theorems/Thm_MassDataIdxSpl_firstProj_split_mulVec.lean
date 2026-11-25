-- Prove2me | Theorems.Thm_MassDataIdxSpl_firstProj_split_mulVec
-- name    : MassDataIdxSpl.firstProj_split_mulVec
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T23:52:20.879379+00:00
-- url     : https://prove2.me/theorems/d1c973dc-f5f8-4236-87fb-065c26737d3d
-- title:
--   Mass Data Idx Spl: first Proj split mul Vec
-- statement:
--   The Mass Data Idx Spl construction uses the first Proj split mul Vec property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LatticeIndices/SecondProjSplitMulVec.lean#L11-L15
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LatticeIndices/SecondProjSplitMulVec.lean#L11-L15

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeIndices_FstMemSpan
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_FundamentalEquivalence_LevelIntersectParabolic
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeIndices_SecondProjSplitMulVec
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MassDataIdxSpl
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Matrix
open scoped TensorProduct

theorem MassDataIdxSpl.firstProj_split_mulVec {K T : Type} [Field K] [CommRing T] [Algebra K T] (θ : T ≃ₐ[K] K × K) {n : Type}
    [Fintype n] (M : Matrix n n T) (v : n → T) :
    pr1 θ (M *ᵥ v) = (M.map fun t => (θ t).1) *ᵥ pr1 θ v := by sorry
