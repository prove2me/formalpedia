-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_WedgeDeriv_sum_adj
-- name    : GlobalTheory.CompanionTheory.WedgeDeriv.sum_adj
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T04:24:41.575476+00:00
-- url     : https://prove2.me/theorems/fcb1bed3-55d3-5807-9abb-c7cbbb9b7957
-- title:
--   Wedge Deriv: sum adj
-- statement:
--   The Wedge Deriv construction uses the sum adj property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/ExteriorDifferentialMatrixUnitFormula.lean#L79-L123
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/ExteriorDifferentialMatrixUnitFormula.lean#L79-L123

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ChainRuleSecondOrder_HasDerivAtDOf
import Definitions.Def_CompanionTheory_AutomorphicTheory_ZuckermanCommutation_ZuckermanFunctors_IsSimpleFam
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_ExteriorDifferentialMatrixUnitFormula
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CompanionTheory.Zuck BranchingSupport Matrix Finset
open scoped InnerProductSpace Kronecker
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.WedgeDeriv

theorem GlobalTheory.CompanionTheory.WedgeDeriv.sum_adj {m n : ℕ} (f g : Fin m → Fin n) (hf : StrictMono f) (hg : StrictMono g) (a b : Fin n) :
    ∑ j, ∑ i, adjugate ((1 : Matrix (Fin n) (Fin n) ℂ).submatrix f g) j i *
      (Matrix.single a b (1 : ℂ)) (f i) (g j) =
    if b ∈ univ.image g ∧ a ∉ (univ.image g).erase b ∧ univ.image f = insert a ((univ.image g).erase b) then
      (-1) ^ (((univ.image g).erase b).filter fun c => c < a).card *
        (-1) ^ (((univ.image g).erase b).filter fun c => c < b).card else 0 := by sorry
