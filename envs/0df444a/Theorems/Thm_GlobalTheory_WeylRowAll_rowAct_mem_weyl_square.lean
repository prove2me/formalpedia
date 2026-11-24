-- Prove2me | Theorems.Thm_GlobalTheory_WeylRowAll_rowAct_mem_weyl_square
-- name    : GlobalTheory.WeylRowAll.rowAct_mem_weyl_square
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T22:32:03.537131+00:00
-- url     : https://prove2.me/theorems/c2d51d42-498e-4fe2-93dc-a3a85b70ba6e
-- title:
--   Weyl Row All: row Act mem weyl square
-- statement:
--   The Weyl Row All construction uses the row Act mem weyl square property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SatakeParameters/WeylRowActionMemWeylLatticeSquare.lean#L156-L159
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SatakeParameters/WeylRowActionMemWeylLatticeSquare.lean#L156-L159

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

theorem GlobalTheory.WeylRowAll.rowAct_mem_weyl_square : ∀ (R : Type) [CommRing R] (n : ℕ) (ν : Fin n → ℕ), Antitone ν →
    ∀ (M : Matrix (Fin n) (Fin n) R), ∀ f ∈ Formalism.GradedWeylDivisibility.weyl R n n le_rfl ν,
      Formalism.GradedWeylDivisibility.rowAct R M f ∈ Formalism.GradedWeylDivisibility.weyl R n n le_rfl ν := by sorry
