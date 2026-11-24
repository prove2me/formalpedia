-- Prove2me | Theorems.Thm_GenFrameSpan_SatP_prod_rename_monomial
-- name    : GenFrameSpan.SatP.prod_rename_monomial
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T10:50:57.998672+00:00
-- url     : https://prove2.me/theorems/54cf096a-2a10-4f2a-a0b3-4633438deefa
-- title:
--   Sat P: prod rename monomial
-- statement:
--   The Sat P construction uses the prod rename monomial property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/MonomialFrameSpan/SatProj.lean#L45-L49
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/MonomialFrameSpan/SatProj.lean#L45-L49

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

theorem GenFrameSpan.SatP.prod_rename_monomial (n : Lt → (ℕ × Fin N0 →₀ ℕ)) :
    ∏ s, rename (emb s) (monomial (n s) (1 : ℤ)) =
      monomial (∑ s, (n s).mapDomain (emb s)) 1 := by sorry
