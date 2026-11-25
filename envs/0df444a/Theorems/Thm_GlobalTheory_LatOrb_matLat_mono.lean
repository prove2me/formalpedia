-- Prove2me | Theorems.Thm_GlobalTheory_LatOrb_matLat_mono
-- name    : GlobalTheory.LatOrb.matLat_mono
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T00:29:03.956358+00:00
-- url     : https://prove2.me/theorems/cc8d43c1-f245-4032-8eca-3787cd9eb117
-- title:
--   Lat Orb: mat Lat mono
-- statement:
--   The Lat Orb construction uses the mat Lat mono property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsUnitaryAdjoinLatticeImageEq.lean#L79-L81
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsUnitaryAdjoinLatticeImageEq.lean#L79-L81

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

theorem GlobalTheory.LatOrb.matLat_mono {O : Type} [CommRing O] [Algebra O K] {M N : Submodule O (Fin n → K)}
    (u : Matrix (Fin n) (Fin n) K) (h : M ≤ N) : matLat O u M ≤ matLat O u N := by sorry
