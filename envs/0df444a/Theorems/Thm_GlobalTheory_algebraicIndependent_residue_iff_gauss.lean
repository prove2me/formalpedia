-- Prove2me | Theorems.Thm_GlobalTheory_algebraicIndependent_residue_iff_gauss
-- name    : GlobalTheory.algebraicIndependent_residue_iff_gauss
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T01:24:26.917229+00:00
-- url     : https://prove2.me/theorems/6a7a7fd5-9593-40d8-ade7-f6e3250345ba
-- title:
--   Global Theory: algebraic Independent residue iff gauss
-- statement:
--   The Global Theory construction uses the algebraic Independent residue iff gauss property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GenericRegularity/AlgebraicIndependentResidueIffGauss.lean#L43-L80
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GenericRegularity/AlgebraicIndependentResidueIffGauss.lean#L43-L80

import Mathlib
import Definitions.Def_ReciprocityTheory_SemistableReduction_ComapInclusionIsLocalHom
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GenericRegularity_AlgebraicIndependentResidueIffGauss
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
open MvPolynomial

theorem GlobalTheory.algebraicIndependent_residue_iff_gauss (F U : Type) [Field F] [Field U] (f : F →+* U)
    (v : Valuation U (WithZero (Multiplicative ℤ))) (σ : Type) (t : σ → U)
    (ht : ∀ s, t s ∈ v.valuationSubring) :
    (letI := ReciprocityTheory.MultiplicativeHeights.residueAlgebra v.valuationSubring f
     AlgebraicIndependent (IsLocalRing.ResidueField (v.valuationSubring.comap f))
      (fun s => IsLocalRing.residue v.valuationSubring ⟨t s, ht s⟩)) ↔
    ∀ p : MvPolynomial σ F, (∀ α, v (f (p.coeff α)) ≤ 1) → (∃ α, v (f (p.coeff α)) = 1) →
      v (MvPolynomial.eval₂ f t p) = 1 := by sorry
