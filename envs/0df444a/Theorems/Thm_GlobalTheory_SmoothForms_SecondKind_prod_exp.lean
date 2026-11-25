-- Prove2me | Theorems.Thm_GlobalTheory_SmoothForms_SecondKind_prod_exp
-- name    : GlobalTheory.SmoothForms.SecondKind.prod_exp
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T12:25:18.64288+00:00
-- url     : https://prove2.me/theorems/2026ee57-aee2-5380-917a-349c6036850a
-- title:
--   Second Kind: prod exp
-- statement:
--   The Second Kind construction uses the prod exp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HeightProofs/SmoothInExponentialCoordsIffFirstSecondKind.lean#L79-L100
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HeightProofs/SmoothInExponentialCoordsIffFirstSecondKind.lean#L79-L100

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HeightProofs_IsLieDataCircle
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HeightProofs_SmoothInExponentialCoordsIffFirstSecondKind
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.SmoothForms NumberField Matrix
open scoped ContDiff Topology
noncomputable section
open GlobalTheory GlobalTheory.SmoothForms GlobalTheory.SmoothForms.SecondKind
open NormedSpace
variable {𝔸 L G : Type} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [FiniteDimensional ℝ 𝔸] [NormedAddCommGroup L]
  [NormedSpace ℝ L] [Group G] {σ : 𝔸 →ₗ[ℝ] 𝔸} {j : L →ₗ[ℝ] 𝔸} {s : 𝔸 → G}
variable {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]

theorem GlobalTheory.SmoothForms.SecondKind.prod_exp (H : IsLieData σ j s) (J : L →L[ℝ] 𝔸) (hJ : ∀ X, J X = j X) (l : List (P →L[ℝ] L)) :
    ∃ c : P → 𝔸, ContDiff ℝ ∞ c ∧ (∀ p, σ (c p) * c p = 1) ∧
      (∀ p, s (c p) = (l.map fun A => expMap j s (A p)).prod) ∧ c 0 = 1 ∧ HasFDerivAt c (J ∘L l.sum) 0 := by sorry
