-- Prove2me | Theorems.Thm_OAI_KadisonKastler_pure_restriction_commuting_factorization
-- name    : OAI.KadisonKastler.pure_restriction_commuting_factorization
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-13T04:49:52.638191+00:00
-- url     : https://prove2.me/theorems/6b9fa25f-72e2-4482-90de-10e275dc2e2e
-- title:
--   OAI.KadisonKastler.pure_restriction_commuting_factorization: intermediate lemma from OpenAI, Universal strong Kadison–Kastler stability (result family 289)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.KadisonKastler.universal_strong_stability`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Universal strong Kadison–Kastler stability (result family 289)*, OpenAI Math Release, September 23, 2026, result family 289, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.KadisonKastler.pure_restriction_commuting_factorization` of [lean/OAI/Analysis/KadisonKastler/PureRestrictionFactorization.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/KadisonKastler/PureRestrictionFactorization.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.KadisonKastler`, with `open NaimarkZFC`):
--
--   ```lean
--   theorem pure_restriction_commuting_factorization
--       (ι : A →⋆ₐ[ℂ] B) (φ : B →L[ℂ] ℂ) (hφ : IsState φ)
--       (hpure : IsPureState (restrictState ι φ))
--       (b : B) (hb : ∀ a : A, Commute b (ι a)) (a : A) :
--       φ (ι a*b)=φ (ι a)*φ b
--   ```
--
--   **Definitions.** The statement is written with `OAI.NaimarkZFC.IsState` (definitions bundle `OAIQ075A006` of this split); `OAI.NaimarkZFC.restrictState` (definitions bundle `OAIQ075A012` of this split); `OAI.NaimarkZFC.IsPureState` (definitions bundle `Q260K007` of this split).
--
--   **Used by.** The proof of `OAI.KadisonKastler.exists_product_state_of_commuting_simple` of this split imports it.
-- source:
--   OpenAI, Universal strong Kadison–Kastler stability (result family 289), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 289; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Universal-strong-Kadison-Kastler-stability-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/KadisonKastler/PureRestrictionFactorization.lean (declaration OAI.KadisonKastler.pure_restriction_commuting_factorization)

import Mathlib
import Mathlib.Analysis.CStarAlgebra.ApproximateUnit
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Normed.Group.Quotient
import Mathlib.Analysis.Normed.Operator.Mul
import Mathlib.RingTheory.Congruence.Basic
import Mathlib.RingTheory.TwoSidedIdeal.Basic
import Mathlib.RingTheory.TwoSidedIdeal.Lattice
import Definitions.Def_Q260K007

section

attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.tensorScalarsInnerProductSpace _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.UltrapowerBridge.instStarRingTracialQuotient _root_.OAI.UltrapowerBridge.instStarTracialQuotient _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

namespace KadisonKastler

open NaimarkZFC

noncomputable section

variable {A B : Type*} [CStarAlgebra A] [CStarAlgebra B]

theorem pure_restriction_commuting_factorization
    (ι : A →⋆ₐ[ℂ] B) (φ : B →L[ℂ] ℂ) (hφ : IsState φ)
    (hpure : IsPureState (restrictState ι φ))
    (b : B) (hb : ∀ a : A, Commute b (ι a)) (a : A) :
    φ (ι a*b)=φ (ι a)*φ b := by
  sorry

end

end KadisonKastler

end OAI
end
