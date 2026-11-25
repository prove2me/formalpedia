-- Prove2me | Theorems.Thm_GlobalTheory_Mem_Col2_ThetaVec_ins_mem
-- name    : GlobalTheory.Mem.Col2.ThetaVec.ins_mem
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T23:32:51.759381+00:00
-- url     : https://prove2.me/theorems/b6b137bd-eaa5-4f2b-90f7-3cf6d49e55c4
-- title:
--   Theta Vec: ins mem
-- statement:
--   The Theta Vec construction uses the ins mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/PeriodLatticeSesquilinearFormIsHerm.lean#L352-L368
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/PeriodLatticeSesquilinearFormIsHerm.lean#L352-L368

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

theorem GlobalTheory.Mem.Col2.ThetaVec.ins_mem {h : Matrix n n ℂ} {Λ : AddSubgroup (n → ℂ)} {α : (n → ℂ) → ℂ} (h0 : α 0 = 1)
    {P : (Fin 4 × n → ℂ) → ℂ} (hP : P ∈ Th (matH (blk4 h)) (fun x => ∏ a, α (slice a x)) (pow4 Λ))
    (z : Fin 4 × n → ℂ) : (fun x => P (ins z x)) ∈ Th (matH h) α Λ := by sorry
