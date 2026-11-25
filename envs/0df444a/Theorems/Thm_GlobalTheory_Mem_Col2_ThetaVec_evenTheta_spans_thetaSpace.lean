-- Prove2me | Theorems.Thm_GlobalTheory_Mem_Col2_ThetaVec_evenTheta_spans_thetaSpace
-- name    : GlobalTheory.Mem.Col2.ThetaVec.evenTheta_spans_thetaSpace
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T23:32:37.564855+00:00
-- url     : https://prove2.me/theorems/9fb204ab-aaad-4417-9329-bfea6332f0c3
-- title:
--   Theta Vec: even Theta spans theta Space
-- statement:
--   The Theta Vec construction uses the even Theta spans theta Space property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/PeriodLatticeSesquilinearFormIsHerm.lean#L132-L155
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/PeriodLatticeSesquilinearFormIsHerm.lean#L132-L155

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

theorem GlobalTheory.Mem.Col2.ThetaVec.evenTheta_spans_thetaSpace {ω₀ : ℂ} (h0 : ω₀ / 2 ∉ L.lattice) {G : ℂ → ℂ} (hG : Differentiable ℂ G)
    (hlaw : ∀ ω ∈ L.lattice, ∀ z, F.thetaZeroCharacter L ω₀ ω * opU (form1 L) ω G z = G z) (z : ℂ) :
    G z = G 0 * F.th0 L (ω₀ / 2) z := by sorry
