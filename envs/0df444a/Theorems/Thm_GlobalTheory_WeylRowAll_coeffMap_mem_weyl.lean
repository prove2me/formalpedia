-- Prove2me | Theorems.Thm_GlobalTheory_WeylRowAll_coeffMap_mem_weyl
-- name    : GlobalTheory.WeylRowAll.coeffMap_mem_weyl
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T22:41:36.701332+00:00
-- url     : https://prove2.me/theorems/dedc930b-75f3-4ad9-8e92-96cc687c9914
-- title:
--   Weyl Row All: coeff Map mem weyl
-- statement:
--   The Weyl Row All construction uses the coeff Map mem weyl property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SatakeParameters/WeylRowActionMemWeylLatticeSquare.lean#L24-L55
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SatakeParameters/WeylRowActionMemWeylLatticeSquare.lean#L24-L55

import Mathlib
import Definitions.Def_Formalism_GradedWeylDivisibility_DualWeylDominanceOf
import Definitions.Def_Formalism_SatakeDualWeyl_KpqSubgroupCompact
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LClosedeqLemmas
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SatakeParameters_WeylRowActionMemWeylLatticeSquare
import Theorems.Thm_Formalism_UG_Final_KpqSubgroupCompact

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial
noncomputable section
open GlobalTheory GlobalTheory.WeylRowAll

theorem GlobalTheory.WeylRowAll.coeffMap_mem_weyl {R S : Type} [CommRing R] [CommRing S] (φ : R →+* S) (c : S →+ R)
    (hc : ∀ (s : S) (a : R), c (s * φ a) = c s * a) {r n : ℕ} (hn : n ≤ r) (ν : Fin n → ℕ)
    (F : MvPolynomial (Fin r × Fin n) S) (hF : F ∈ Formalism.GradedWeylDivisibility.weyl S r n hn ν) :
    coeffMap c F ∈ Formalism.GradedWeylDivisibility.weyl R r n hn ν := by sorry
