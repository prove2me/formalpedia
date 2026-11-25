-- Prove2me | Theorems.Thm_GlobalTheory_LatOrb_matLat_le
-- name    : GlobalTheory.LatOrb.matLat_le
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T00:29:20.976601+00:00
-- url     : https://prove2.me/theorems/63d23070-1453-4997-bf32-230b020bd947
-- title:
--   Lat Orb: mat Lat le
-- statement:
--   The Lat Orb construction uses the mat Lat le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsUnitaryAdjoinLatticeImageEq.lean#L73-L77
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsUnitaryAdjoinLatticeImageEq.lean#L73-L77

import Mathlib
import Definitions.Def_Formalism_SatakeDualWeyl_Statement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_MemMatLat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IntegralAevalEqAevalMapOfCoprimeCharpolyStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsIntegralMatrixOfMapsToFullRankLatticeStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsUnitaryMulIntegralOfNormMaximalOrderUnitStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsUnitaryAdjoinLatticeImageEq
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

theorem GlobalTheory.LatOrb.matLat_le {O : Type} [CommRing O] [Algebra O K] (M : Submodule O (Fin n → K))
    (u : Matrix (Fin n) (Fin n) K) (hu : ∀ v ∈ M, u *ᵥ v ∈ M) : matLat O u M ≤ M := by sorry
