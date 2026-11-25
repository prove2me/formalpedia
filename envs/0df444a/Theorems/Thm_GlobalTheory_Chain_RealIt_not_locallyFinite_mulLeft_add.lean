-- Prove2me | Theorems.Thm_GlobalTheory_Chain_RealIt_not_locallyFinite_mulLeft_add
-- name    : GlobalTheory.Chain.RealIt.not_locallyFinite_mulLeft_add
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T11:58:18.32134+00:00
-- url     : https://prove2.me/theorems/70f2513d-f49e-49b0-9079-e4bf725ddc22
-- title:
--   Real It: not locally Finite mul Left add
-- statement:
--   The Real It construction uses the not locally Finite mul Left add property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/NotLocallyFiniteQuadraticMulAddDegreeNonraising.lean#L28-L48
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/NotLocallyFiniteQuadraticMulAddDegreeNonraising.lean#L28-L48

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

theorem GlobalTheory.Chain.RealIt.not_locallyFinite_mulLeft_add :
    ∀ (σ : Type) [Finite σ] (Q : MvPolynomial σ ℂ) (L : Module.End ℂ (MvPolynomial σ ℂ)),
      Q ≠ 0 → Q.IsHomogeneous 2 → (∀ P, (L P).totalDegree ≤ P.totalDegree) →
      ∀ φ : MvPolynomial σ ℂ, φ ≠ 0 → ∀ F : Submodule ℂ (MvPolynomial σ ℂ),
        FiniteDimensional ℂ F → ¬ ∀ n : ℕ, ((LinearMap.mulLeft ℂ Q + L) ^ n) φ ∈ F := by sorry
