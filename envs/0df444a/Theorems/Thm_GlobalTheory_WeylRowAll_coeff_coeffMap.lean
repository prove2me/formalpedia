-- Prove2me | Theorems.Thm_GlobalTheory_WeylRowAll_coeff_coeffMap
-- name    : GlobalTheory.WeylRowAll.coeff_coeffMap
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T22:32:16.870049+00:00
-- url     : https://prove2.me/theorems/1beb7e07-d623-4c6d-9b82-eb7218518c13
-- title:
--   Weyl Row All: coeff coeff Map
-- statement:
--   The Weyl Row All construction uses the coeff coeff Map property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SatakeParameters/WeylRowActionMemWeylLatticeSquare.lean#L16-L22
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SatakeParameters/WeylRowActionMemWeylLatticeSquare.lean#L16-L22

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

theorem GlobalTheory.WeylRowAll.coeff_coeffMap {R S σ : Type} [CommRing R] [CommRing S] (c : S →+ R)
    (F : MvPolynomial σ S) (m : σ →₀ ℕ) : coeff m (coeffMap c F) = c (coeff m F) := by sorry
