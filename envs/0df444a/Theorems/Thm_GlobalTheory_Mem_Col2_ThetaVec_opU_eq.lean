-- Prove2me | Theorems.Thm_GlobalTheory_Mem_Col2_ThetaVec_opU_eq
-- name    : GlobalTheory.Mem.Col2.ThetaVec.opU_eq
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T23:32:45.092645+00:00
-- url     : https://prove2.me/theorems/da7e1e5d-c410-402e-b722-2225be6615da
-- title:
--   Theta Vec: op U eq
-- statement:
--   The Theta Vec construction uses the op U eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/PeriodLatticeSesquilinearFormIsHerm.lean#L61-L63
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/PeriodLatticeSesquilinearFormIsHerm.lean#L61-L63

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_ProductThetaMem
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_HasSumLocallyUniformlyWeierstrassZetaExcept
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_IntegralDensEqZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_PeriodLatticeSesquilinearFormIsHerm
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.ThetaVec
open Formalism.L2.Th1 Formalism.L2.Th1.H Complex GlobalTheory.ThetaInter
open scoped BigOperators ComplexConjugate Real
variable (L : PeriodPair)

theorem GlobalTheory.Mem.Col2.ThetaVec.opU_eq (x : ℂ) (G : ℂ → ℂ) : F.opU L x G = opU (form1 L) x G := by sorry
