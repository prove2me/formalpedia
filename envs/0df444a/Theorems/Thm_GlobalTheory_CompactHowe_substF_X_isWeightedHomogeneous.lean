-- Prove2me | Theorems.Thm_GlobalTheory_CompactHowe_substF_X_isWeightedHomogeneous
-- name    : GlobalTheory.CompactHowe.substF_X_isWeightedHomogeneous
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T21:49:11.880804+00:00
-- url     : https://prove2.me/theorems/2eaba7aa-2b19-4574-8709-a6224f20c633
-- title:
--   Compact Howe: subst F X is Weighted Homogeneous
-- statement:
--   The Compact Howe construction uses the subst F X is Weighted Homogeneous property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/MapDomainFstEqOfCoeffMatrixFamilyBilateralSubsti.lean#L16-L25
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/MapDomainFstEqOfCoeffMatrixFamilyBilateralSubsti.lean#L16-L25

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_TotalDegreeSubstFLe
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_MapDomainFstEqOfCoeffMatrixFamilyBilateralSubsti
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MvPolynomial
open GlobalTheory GlobalTheory.CompactHowe

theorem GlobalTheory.CompactHowe.substF_X_isWeightedHomogeneous {ι : Type} {N n : ℕ} (h : ι → Matrix (Fin N) (Fin N) ℂ)
    (g : ι → Matrix (Fin n) (Fin n) ℂ) (p : ι × Fin N × Fin n) :
    IsWeightedHomogeneous (fun p : ι × Fin N × Fin n => (Finsupp.single p.1 1 : ι →₀ ℕ))
      (substF h g (X p)) (Finsupp.single p.1 1) := by sorry
