-- Prove2me | Theorems.Thm_GenFrameSpan_SatP_nablaX_eq
-- name    : GenFrameSpan.SatP.nablaX_eq
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T07:08:07.802928+00:00
-- url     : https://prove2.me/theorems/0c12d8d1-60cf-4795-a170-75fcbd011915
-- title:
--   Sat P: nabla X eq
-- statement:
--   The Sat P construction uses the nabla X eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/MonomialFrameSpan/SatProj.lean#L51-L60
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/MonomialFrameSpan/SatProj.lean#L51-L60

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

theorem GenFrameSpan.SatP.nablaX_eq (nu : Lt → YoungDiagram) (J : ColChoice N0 nu) :
    nablaX N0 nu J = ∏ s, rename (emb s) (∏ c : Fin ((nu s).rowLen 0), minorX ℤ N0 ((nu s).colLen c) (J s c)) := by sorry
