-- Prove2me | Theorems.Thm_GlobalTheory_Chevalley_exists_le_maximalIdeal_pow_smul_of_directed
-- name    : GlobalTheory.Chevalley.exists_le_maximalIdeal_pow_smul_of_directed
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T11:09:15.75702+00:00
-- url     : https://prove2.me/theorems/3106a725-65ae-4795-8683-465c0ed3bbeb
-- title:
--   Chevalley: exists le maximal Ideal pow smul of directed
-- statement:
--   The Chevalley construction uses the exists le maximal Ideal pow smul of directed property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ExistsLeMaximalIdealPowSmulOfDirected.lean#L147-L232
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ExistsLeMaximalIdealPowSmulOfDirected.lean#L147-L232

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
open TensorProduct Polynomial IsLocalRing

theorem GlobalTheory.Chevalley.exists_le_maximalIdeal_pow_smul_of_directed :
    ∀ (B M ι : Type) [CommRing B] [IsLocalRing B] [IsNoetherianRing B]
      [IsAdicComplete (maximalIdeal B) B] [AddCommGroup M] [Module B M] [Module.Finite B M]
      (K : ι → Submodule B M), Nonempty ι → Directed (· ≥ ·) K → (⨅ i, K i) = ⊥ →
      ∀ N : ℕ, ∃ i, K i ≤ maximalIdeal B ^ N • (⊤ : Submodule B M) := by sorry
