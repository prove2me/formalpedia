-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_Sobolev_opBound_Q_locM
-- name    : GroundTheory.Automorphic.Sobolev.opBound_Q_locM
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T05:21:23.523167+00:00
-- url     : https://prove2.me/theorems/0f9875de-b6bd-4d27-8a09-3019851f8d25
-- title:
--   Sobolev: op Bound Q loc M
-- statement:
--   The Sobolev construction uses the op Bound Q loc M property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/PartialDifferential/EllipticLocal.lean#L602-L639
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/PartialDifferential/EllipticLocal.lean#L602-L639

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_PartialDifferential_EllipticOperators
import Definitions.Def_GroundTheory_AutomorphicForms_PartialDifferential_EllipticLocal
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Automorphic GroundTheory.Automorphic.Sobolev
open TemperedDistribution MeasureTheory FourierTransform LineDeriv
open scoped SchwartzMap ENNReal ContDiff
noncomputable section
set_option linter.unusedSectionVars false
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
variable {m n : ℕ} (a : Fin n → 𝓢(E, ℂ)) (w : Fin n → Fin m → E) (N : 𝓢'(E, ℂ) →L[ℂ] 𝓢'(E, ℂ))
  (x₀ : E)

theorem GroundTheory.Automorphic.Sobolev.opBound_Q_locM {δ : ℝ} (hδ : 0 < δ) (Q : 𝓢'(E, ℂ) →L[ℂ] 𝓢'(E, ℂ)) (s : ℝ)
    {η CQ κ : ℝ} (hη : 0 ≤ η) (hCQ : 0 ≤ CQ) (hκ : 0 ≤ κ)
    (hg : ∀ i x, ‖locCoeff a x₀ hδ i x‖ ≤ η)
    (hQ : OpBound Q (s - m) s CQ) (hQs : OpBound Q (s - m + 1) s κ)
    {Cr : Fin n → ℝ} (hCr0 : ∀ i, 0 ≤ Cr i)
    (hCr : ∀ i, OpBound (mulRem (locCoeff a x₀ hδ i) (s - m)) (s - m) (s - m + 1) (Cr i))
    {CN : ℝ} (hCN0 : 0 ≤ CN) (hCN : OpBound N s (s - m + 1) CN) :
    OpBound (Q ∘L locM a w N x₀ hδ) s s
      (CQ * (η * ∑ i, ∏ j, (2 * Real.pi * ‖w i j‖)) +
        κ * (∑ i, Cr i * ∏ j, (2 * Real.pi * ‖w i j‖) + mulConst (s - m + 1) (bump x₀ hδ) * CN)) := by sorry
