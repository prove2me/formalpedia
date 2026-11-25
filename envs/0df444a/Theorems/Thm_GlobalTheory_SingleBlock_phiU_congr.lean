-- Prove2me | Theorems.Thm_GlobalTheory_SingleBlock_phiU_congr
-- name    : GlobalTheory.SingleBlock.phiU_congr
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T23:50:18.320807+00:00
-- url     : https://prove2.me/theorems/365ff25e-7cbd-45a9-8bdd-24664b6634e4
-- title:
--   Single Block: phi U congr
-- statement:
--   The Single Block construction uses the phi U congr property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/HasCompactSupportPhiU.lean#L133-L144
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/HasCompactSupportPhiU.lean#L133-L144

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

theorem GlobalTheory.SingleBlock.phiU_congr (hϖ : ϖ ∈ O) (hϖ0 : ϖ ≠ 0) (hloc : IsLocalAt O ϖ)
    (hKP : congSub O ϖ r ≤ P) (hP : P ≤ GLint O r) (ρ : P →* ℂˣ)
    (hρ : ∀ (k : GL (Fin r) F) (hk : k ∈ congSub O ϖ r), ρ ⟨k, hKP hk⟩ = 1)
    {x y : Matrix (Fin r ⊕ Fin t) (Fin r) F} (hy : ∀ i j, ϖ⁻¹ * (y i j - x i j) ∈ O) :
    phiU O ϖ P ρ y = phiU O ϖ P ρ x := by sorry
