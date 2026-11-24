-- Prove2me | Theorems.Thm_GenFrameSpan_SatP_prod_mem_span
-- name    : GenFrameSpan.SatP.prod_mem_span
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T10:50:51.592836+00:00
-- url     : https://prove2.me/theorems/11fbd6a0-54d9-4ce3-8559-99a245886553
-- title:
--   Sat P: prod mem span
-- statement:
--   The Sat P construction uses the prod mem span property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/MonomialFrameSpan/SatProj.lean#L134-L187
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/MonomialFrameSpan/SatProj.lean#L134-L187

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MonomialFrameSpan_SatDefs
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MonomialFrameSpan_SatProj
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Classical
open GenFrameSpan
open CutKW MvPolynomial
open GenFrameSpan.SatP
variable {Lt : Type} [Fintype Lt] [DecidableEq Lt] {N0 : ℕ}

theorem GenFrameSpan.SatP.prod_mem_span (nu : Lt → YoungDiagram) (g : Lt → MvPolynomial (ℕ × Fin N0) ℤ)
    (hg : ∀ s, g s ∈ nablaSpan ℤ N0 (nu s)) :
    ∏ s, rename (emb s) (g s) ∈ Submodule.span ℤ (Set.range (nablaX N0 nu)) := by sorry
