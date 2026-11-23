-- Prove2me | Theorems.Thm_GenFrameSpan_SatP_Tmap_monomial
-- name    : GenFrameSpan.SatP.Tmap_monomial
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T07:08:28.954186+00:00
-- url     : https://prove2.me/theorems/88db3ef2-9935-47d7-bf33-13a13185cf40
-- title:
--   Sat P: Tmap monomial
-- statement:
--   The Sat P construction uses the Tmap monomial property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/MonomialFrameSpan/SatProj.lean#L67-L73
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/MonomialFrameSpan/SatProj.lean#L67-L73

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

theorem GenFrameSpan.SatP.Tmap_monomial (π : Lt → (MvPolynomial (ℕ × Fin N0) ℤ →ₗ[ℤ] MvPolynomial (ℕ × Fin N0) ℤ))
    (m : Lt × ℕ × Fin N0 →₀ ℕ) :
    Tmap π (monomial m 1) = ∏ s, rename (emb s) (π s (monomial (res s m) 1)) := by sorry
