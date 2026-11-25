-- Prove2me | Theorems.Thm_GlobalTheory_Chevalley_exists_le_sup_maximalIdeal_pow_smul
-- name    : GlobalTheory.Chevalley.exists_le_sup_maximalIdeal_pow_smul
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T11:58:30.962177+00:00
-- url     : https://prove2.me/theorems/f9efb3b1-1979-4772-9189-4921efa0b2cb
-- title:
--   Chevalley: exists le sup maximal Ideal pow smul
-- statement:
--   The Chevalley construction uses the exists le sup maximal Ideal pow smul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ExistsLeMaximalIdealPowSmulOfDirected.lean#L39-L56
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ExistsLeMaximalIdealPowSmulOfDirected.lean#L39-L56

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_FiniteCocycles
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_MatMapTmul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_FiniteAlgebraLocalCompletion
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsLeMaximalIdealPowSmulOfDirected
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open TensorProduct Polynomial IsLocalRing GlobalTheory.Pat
open GlobalTheory GlobalTheory.Chevalley

theorem GlobalTheory.Chevalley.exists_le_sup_maximalIdeal_pow_smul (B M ι : Type) [CommRing B] [IsLocalRing B]
    [IsNoetherianRing B] [AddCommGroup M] [Module B M] [Module.Finite B M] (K : ι → Submodule B M)
    [Nonempty ι] (hK : Directed (· ≥ ·) K) (k : ℕ) :
    ∃ i, ∀ j, K i ≤ K j ⊔ maximalIdeal B ^ k • (⊤ : Submodule B M) := by sorry
