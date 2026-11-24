-- Prove2me | Theorems.Thm_GlobalTheory_JointHarm_mapDomain_add_inj
-- name    : GlobalTheory.JointHarm.mapDomain_add_inj
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T22:26:52.514815+00:00
-- url     : https://prove2.me/theorems/e20d4ff5-d233-4e2c-be1f-068fc6df5056
-- title:
--   Joint Harm: map Domain add inj
-- statement:
--   The Joint Harm construction uses the map Domain add inj property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/JointHarmonicOfHookNorm.lean#L53-L64
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/JointHarmonicOfHookNorm.lean#L53-L64

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_TorsionBlocks_LowerUnipotentMinors
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_TorsionBlocks_BottomMinor
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_JointHarmonicOfHookNorm
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.JointHarm
open MvPolynomial Matrix GlobalTheory.IndefiniteRowSideFullHecke.SubstitutionPolynomials
variable {n p q : ℕ}
open Formalism.E
variable {σ₁ σ₂ τ : Type} {f : σ₁ → τ} {g : σ₂ → τ}

theorem GlobalTheory.JointHarm.mapDomain_add_inj (hf : Function.Injective f) (hg : Function.Injective g)
    (hfg : ∀ x y, f x ≠ g y) {α α' : σ₁ →₀ ℕ} {β β' : σ₂ →₀ ℕ}
    (h : α.mapDomain f + β.mapDomain g = α'.mapDomain f + β'.mapDomain g) : α = α' ∧ β = β' := by sorry
