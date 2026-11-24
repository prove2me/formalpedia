-- Prove2me | Theorems.Thm_GlobalTheory_IndefiniteRowSideFullHecke_LocalIntegralGL_weilPair_one_right
-- name    : GlobalTheory.IndefiniteRowSideFullHecke.LocalIntegralGL.weilPair_one_right
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T23:49:08.289879+00:00
-- url     : https://prove2.me/theorems/255f9a66-0585-4044-a164-a8d3513a4ff5
-- title:
--   Local Integral GL: weil Pair one right
-- statement:
--   The Local Integral GL construction uses the weil Pair one right property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/TorsionBlocks/LocalIntegralGL.lean#L25-L29
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/TorsionBlocks/LocalIntegralGL.lean#L25-L29

import Mathlib
import Definitions.Def_Formalism_DoubleCosetMeasures_StatementV
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_TorsionBlocks_LocalIntegralGL
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Matrix ComplexConjugate ValuativeRel Formalism.DoubleCosetMeasures
open GlobalTheory GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.IndefiniteRowSideFullHecke.LocalIntegralGL
variable {F : Type} [Field F] {r t : ℕ}

theorem GlobalTheory.IndefiniteRowSideFullHecke.LocalIntegralGL.weilPair_one_right (μ η : Fˣ →* ℂˣ) (nrm : AbsoluteValue F ℝ) (g : GL (Fin r) F)
    (Φ : Matrix (Fin r ⊕ Fin t) (Fin r) F → ℂ) :
    weilPair μ η nrm g 1 Φ = omegaS (μ * η) nrm g Φ := by sorry
