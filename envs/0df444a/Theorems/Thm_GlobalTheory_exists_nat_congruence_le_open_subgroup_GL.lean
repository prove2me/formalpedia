-- Prove2me | Theorems.Thm_GlobalTheory_exists_nat_congruence_le_open_subgroup_GL
-- name    : GlobalTheory.exists_nat_congruence_le_open_subgroup_GL
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T22:35:32.762379+00:00
-- url     : https://prove2.me/theorems/68648e8f-ca4e-477c-8684-30132e5c7381
-- title:
--   Global Theory: exists nat congruence le open subgroup GL
-- statement:
--   The Global Theory construction uses the exists nat congruence le open subgroup GL property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/ExistsNatCongruenceLeOpenSubgroupGL.lean#L19-L52
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/ExistsNatCongruenceLeOpenSubgroupGL.lean#L19-L52

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_GaloisLevelStructure_DefsAut
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_ExistsNatCongruenceLeOpenSubgroupGL
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2
open GlobalTheory

theorem GlobalTheory.exists_nat_congruence_le_open_subgroup_GL :
    ∀ (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) (n : ℕ)
    (K : Subgroup (GL (Fin n) (v.adicCompletion F))), IsOpen (K : Set (GL (Fin n) (v.adicCompletion F))) →
    ∃ M : ℕ, 0 < M ∧ ∀ g : GL (Fin n) (v.adicCompletion F),
      (∀ i j, Valued.v ((g : Matrix (Fin n) (Fin n) (v.adicCompletion F)) i j - (1 : Matrix (Fin n) (Fin n) (v.adicCompletion F)) i j) ≤
        Valued.v ((M : v.adicCompletion F))) →
      (∀ i j, Valued.v (((g⁻¹ : GL (Fin n) (v.adicCompletion F)) : Matrix (Fin n) (Fin n) (v.adicCompletion F)) i j -
        (1 : Matrix (Fin n) (Fin n) (v.adicCompletion F)) i j) ≤ Valued.v ((M : v.adicCompletion F))) → g ∈ K := by sorry
