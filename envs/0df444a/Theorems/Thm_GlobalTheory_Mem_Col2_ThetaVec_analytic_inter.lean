-- Prove2me | Theorems.Thm_GlobalTheory_Mem_Col2_ThetaVec_analytic_inter
-- name    : GlobalTheory.Mem.Col2.ThetaVec.analytic_inter
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T23:33:22.02472+00:00
-- url     : https://prove2.me/theorems/75d660d0-3157-4cad-b1b5-0caceb59be11
-- title:
--   Theta Vec: analytic inter
-- statement:
--   The Theta Vec construction uses the analytic inter property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/PeriodLatticeSesquilinearFormIsHerm.lean#L416-L426
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/PeriodLatticeSesquilinearFormIsHerm.lean#L416-L426

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
variable {n : Type} [Fintype n]

theorem GlobalTheory.Mem.Col2.ThetaVec.analytic_inter (H : Sesq (n → ℂ)) (α : (n → ℂ) → ℂ) (A₁ A₂ : AddSubgroup (n → ℂ))
    [Finite (A₂ ⧸ A₁.addSubgroupOf A₂)] {G : (n → ℂ) → ℂ} (hG : AnalyticOnNhd ℂ G Set.univ) :
    AnalyticOnNhd ℂ (inter H α A₁ A₂ G) Set.univ := by sorry
