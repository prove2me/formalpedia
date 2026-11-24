-- Prove2me | Theorems.Thm_GlobalTheory_SingleBlock_mul_left_mem
-- name    : GlobalTheory.SingleBlock.mul_left_mem
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T23:50:06.080637+00:00
-- url     : https://prove2.me/theorems/13576a1e-994f-42f8-81ee-b34e493575cd
-- title:
--   Single Block: mul left mem
-- statement:
--   The Single Block construction uses the mul left mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/HasCompactSupportPhiU.lean#L84-L108
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/HasCompactSupportPhiU.lean#L84-L108

import Mathlib
import Definitions.Def_Formalism_DoubleCosetMeasures_LatticeCoset
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_TorsionBlocks_LocalIntegralGL
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_HasCompactSupportPhiU
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Matrix ComplexConjugate Formalism.DoubleCosetMeasures Formalism.DoubleCosetMeasures.P GlobalTheory.IndefiniteRowSideFullHecke.LocalIntegralGL
open GlobalTheory GlobalTheory.SingleBlock
variable {F : Type} [Field F] {r t : ℕ} {O : Subring F} {ϖ : F} {P : Subgroup (GL (Fin r) F)}

theorem GlobalTheory.SingleBlock.mul_left_mem (hϖ : ϖ ∈ O) (hϖ0 : ϖ ≠ 0) (hloc : IsLocalAt O ϖ)
    (hKP : congSub O ϖ r ≤ P) (hP : P ≤ GLint O r) (ρ : P →* ℂˣ)
    (hρ : ∀ (k : GL (Fin r) F) (hk : k ∈ congSub O ϖ r), ρ ⟨k, hKP hk⟩ = 1)
    {h : Matrix (Fin r ⊕ Fin t) (Fin r ⊕ Fin t) F} (hh : ∀ i j, h i j ∈ O) (k : P)
    (hk : ((k : GL (Fin r) F) : Matrix (Fin r) (Fin r) F) = h.toBlocks₁₁)
    (hc : h.toBlocks₂₁ ∈ IIset O ϖ)
    {x : Matrix (Fin r ⊕ Fin t) (Fin r) F} (hx : x ∈ suppSet t O ϖ P) :
    h * x ∈ suppSet t O ϖ P ∧ phiU O ϖ P ρ (h * x) = ((ρ k : ℂˣ) : ℂ) * phiU O ϖ P ρ x := by sorry
