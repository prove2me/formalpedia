-- Prove2me | Theorems.Thm_GlobalTheory_T_rename_upperLeftCorner_mem_weylLattice
-- name    : GlobalTheory.T.rename_upperLeftCorner_mem_weylLattice
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T22:46:33.950082+00:00
-- url     : https://prove2.me/theorems/ff99d5be-1340-488c-aad8-c5dfdc6cf2d0
-- title:
--   T: rename upper Left Corner mem weyl Lattice
-- statement:
--   The T construction uses the rename upper Left Corner mem weyl Lattice property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SatakeParameters/RenameUpperLeftCornerMemWeylLatticeStatement.lean#L8-L9
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SatakeParameters/RenameUpperLeftCornerMemWeylLatticeStatement.lean#L8-L9

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SatakeParameters_RenameUpperLeftCornerMemWeylLattice
import Mathlib
import Definitions.Def_Formalism_GradedWeylDivisibility_DualWeylDominanceOf
import Definitions.Def_Formalism_SatakeDualWeyl_KpqSubgroupCompact
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LClosedeqLemmas
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SatakeParameters_RenameUpperLeftCornerMemWeylLatticeStatement
import Theorems.Thm_Formalism_UG_Final_KpqSubgroupCompact

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

set_option maxHeartbeats 1000000

theorem GlobalTheory.T.rename_upperLeftCorner_mem_weylLattice : ∀ (R : Type) [CommRing R] (a b : ℕ) (hab : a ≤ b) (ν : Fin a → ℕ) (ν' : Fin b → ℕ), (∀ j : Fin b, ν' j = if h : (j : ℕ) < a then ν ⟨j, h⟩ else 0) → ∀ f ∈ Formalism.GradedWeylDivisibility.weyl R a a le_rfl ν, MvPolynomial.rename (fun v : Fin a × Fin a => ((Fin.castLE hab v.1, Fin.castLE hab v.2) : Fin b × Fin b)) f ∈ Formalism.GradedWeylDivisibility.weyl R b b le_rfl ν' := by sorry
