-- Prove2me | Theorems.Thm_GlobalTheory_Mem_Col2_ThetaVec_productEvenTheta_mem_thetaSpace
-- name    : GlobalTheory.Mem.Col2.ThetaVec.productEvenTheta_mem_thetaSpace
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T23:32:37.725553+00:00
-- url     : https://prove2.me/theorems/1f7544b9-67f7-478a-8b74-879d52a83089
-- title:
--   Theta Vec: product Even Theta mem theta Space
-- statement:
--   The Theta Vec construction uses the product Even Theta mem theta Space property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/PeriodLatticeSesquilinearFormIsHerm.lean#L269-L278
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/PeriodLatticeSesquilinearFormIsHerm.lean#L269-L278

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
variable {n : Type} [Fintype n] [DecidableEq n]

theorem GlobalTheory.Mem.Col2.ThetaVec.productEvenTheta_mem_thetaSpace (ω₀ : ℂ) {α : (n → ℂ) → ℂ} (hα : ∀ x ∈ stdLat L n, α x = stdChar L ω₀ x) :
    F0 L ω₀ n ∈ Th (stdH L n) α (stdLat L n) := by sorry
