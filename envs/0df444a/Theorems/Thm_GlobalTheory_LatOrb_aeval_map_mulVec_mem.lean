-- Prove2me | Theorems.Thm_GlobalTheory_LatOrb_aeval_map_mulVec_mem
-- name    : GlobalTheory.LatOrb.aeval_map_mulVec_mem
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T00:33:49.746812+00:00
-- url     : https://prove2.me/theorems/4a6e59fb-6bcf-44a1-83e0-43a5f9bd9f6c
-- title:
--   Lat Orb: aeval map mul Vec mem
-- statement:
--   The Lat Orb construction uses the aeval map mul Vec mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsUnitaryAdjoinLatticeImageEq.lean#L54-L71
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsUnitaryAdjoinLatticeImageEq.lean#L54-L71

import Mathlib
import Definitions.Def_Formalism_SatakeDualWeyl_Statement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_MemMatLat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IntegralAevalEqAevalMapOfCoprimeCharpolyStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsIntegralMatrixOfMapsToFullRankLatticeStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsUnitaryMulIntegralOfNormMaximalOrderUnitStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsUnitaryAdjoinLatticeImageEq
import Theorems.Thm_GlobalTheory_FormalIsogeny_FiniteReduction_map

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial Matrix GlobalTheory.LatOrb
noncomputable section
open GlobalTheory GlobalTheory.LatOrb
variable {K : Type} [Field K] {n : ℕ}

theorem GlobalTheory.LatOrb.aeval_map_mulVec_mem {O : Type} [CommRing O] [Algebra O K] (M : Submodule O (Fin n → K))
    (γ : Matrix (Fin n) (Fin n) K) (hM : ∀ v ∈ M, γ *ᵥ v ∈ M) (r : O[X]) :
    ∀ v ∈ M, aeval γ (r.map (algebraMap O K)) *ᵥ v ∈ M := by sorry
