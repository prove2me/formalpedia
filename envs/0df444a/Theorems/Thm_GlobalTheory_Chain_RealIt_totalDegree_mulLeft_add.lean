-- Prove2me | Theorems.Thm_GlobalTheory_Chain_RealIt_totalDegree_mulLeft_add
-- name    : GlobalTheory.Chain.RealIt.totalDegree_mulLeft_add
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T11:07:36.1528+00:00
-- url     : https://prove2.me/theorems/f4964fa9-6cb7-440e-8211-d49169d992f9
-- title:
--   Real It: total Degree mul Left add
-- statement:
--   The Real It construction uses the total Degree mul Left add property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/NotLocallyFiniteQuadraticMulAddDegreeNonraising.lean#L7-L16
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/NotLocallyFiniteQuadraticMulAddDegreeNonraising.lean#L7-L16

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_NotLocallyFiniteQuadraticMulAddDegreeNonraising
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.Chain GlobalTheory.Chain.RealIt
open MvPolynomial

theorem GlobalTheory.Chain.RealIt.totalDegree_mulLeft_add {σ : Type} (Q : MvPolynomial σ ℂ)
    (L : Module.End ℂ (MvPolynomial σ ℂ)) (hQ : Q ≠ 0) (hh : Q.IsHomogeneous 2)
    (hL : ∀ P, (L P).totalDegree ≤ P.totalDegree) (φ : MvPolynomial σ ℂ) (hφ : φ ≠ 0) :
    ((LinearMap.mulLeft ℂ Q + L) φ).totalDegree = φ.totalDegree + 2 := by sorry
