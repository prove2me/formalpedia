-- Prove2me | Theorems.Thm_GlobalTheory_LatOrb_exists_cyclicVector_of_separable_charpoly
-- name    : GlobalTheory.LatOrb.exists_cyclicVector_of_separable_charpoly
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T21:24:33.131422+00:00
-- url     : https://prove2.me/theorems/ddc62311-b573-470d-b66c-859fd10c5f82
-- title:
--   Lat Orb: exists cyclic Vector of separable charpoly
-- statement:
--   The Lat Orb construction uses the exists cyclic Vector of separable charpoly property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsCyclicVectorOfSeparableCharpoly.lean#L10-L22
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsCyclicVectorOfSeparableCharpoly.lean#L10-L22

import Mathlib
import Definitions.Def_Formalism_SatakeDualWeyl_Statement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_MemMatLat
import Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_ExistsNeZeroAevalEqZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsCyclicVectorOfSeparableCharpoly
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial Matrix GlobalTheory.LatOrb
open GlobalTheory GlobalTheory.LatOrb

theorem GlobalTheory.LatOrb.exists_cyclicVector_of_separable_charpoly {K : Type} [Field K] (n : ℕ)
    (γ : Matrix (Fin n) (Fin n) K) (hs : γ.charpoly.Separable) :
    ∃ v₀ : Fin n → K, ∀ u : Fin n → K, ∃ p : K[X], u = aeval γ p *ᵥ v₀ := by sorry
