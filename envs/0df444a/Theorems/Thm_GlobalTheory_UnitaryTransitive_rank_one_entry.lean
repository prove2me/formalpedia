-- Prove2me | Theorems.Thm_GlobalTheory_UnitaryTransitive_rank_one_entry
-- name    : GlobalTheory.UnitaryTransitive.rank_one_entry
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T21:45:31.980035+00:00
-- url     : https://prove2.me/theorems/1c5fc41a-74aa-41ea-8127-e45ce9c5ae3a
-- title:
--   Unitary Transitive: rank one entry
-- statement:
--   The Unitary Transitive construction uses the rank one entry property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/IntegralUnitaryGroupTransitiveNormOneVectors.lean#L32-L37
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/IntegralUnitaryGroupTransitiveNormOneVectors.lean#L32-L37

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_FourierMatch
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_UnimodularHermitianMatrixCongruentOneStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IntegralUnitaryGroupTransitiveNormOneVectors
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
open GlobalTheory GlobalTheory.UnitaryTransitive
variable {E : Type} [Field E] [StarRing E]

theorem GlobalTheory.UnitaryTransitive.rank_one_entry {r : ℕ} (g : Matrix (Fin r) (Fin r) E) (a b : Fin r → E) (m m' : Fin r) :
    (gᴴ * (replicateCol Unit a * replicateRow Unit b) * g) m m' = (gᴴ *ᵥ a) m * (b ᵥ* g) m' := by sorry
