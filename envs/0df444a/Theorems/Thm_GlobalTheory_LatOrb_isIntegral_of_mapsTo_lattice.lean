-- Prove2me | Theorems.Thm_GlobalTheory_LatOrb_isIntegral_of_mapsTo_lattice
-- name    : GlobalTheory.LatOrb.isIntegral_of_mapsTo_lattice
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T17:58:55.262972+00:00
-- url     : https://prove2.me/theorems/fed8983a-cc84-4cbc-837e-1fef7ea9eafc
-- title:
--   Lat Orb: is Integral of maps To lattice
-- statement:
--   The Lat Orb construction uses the is Integral of maps To lattice property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/IsIntegralMatrixOfMapsToFullRankLattice.lean#L8-L49
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/IsIntegralMatrixOfMapsToFullRankLattice.lean#L8-L49

import Mathlib
import Definitions.Def_Formalism_SatakeDualWeyl_Statement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_MemMatLat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsIntegralMatrixOfMapsToFullRankLattice
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

theorem GlobalTheory.LatOrb.isIntegral_of_mapsTo_lattice : ∀ {O K : Type} [CommRing O] [Field K] [Algebra O K] (n : ℕ) (M : Submodule O (Fin n → K)),
    IsLatV O M → ∀ c : Matrix (Fin n) (Fin n) K, (∀ v ∈ M, c *ᵥ v ∈ M) → IsIntegral O c := by sorry
