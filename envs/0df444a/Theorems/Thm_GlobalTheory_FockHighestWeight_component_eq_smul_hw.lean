-- Prove2me | Theorems.Thm_GlobalTheory_FockHighestWeight_component_eq_smul_hw
-- name    : GlobalTheory.FockHighestWeight.component_eq_smul_hw
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T13:34:42.992557+00:00
-- url     : https://prove2.me/theorems/9261109a-2864-40fa-973a-39928050ff45
-- title:
--   Fock Highest Weight: component eq smul hw
-- statement:
--   The Fock Highest Weight construction uses the component eq smul hw property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/LowerTriOfInterlaced.lean#L135-L156
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/LowerTriOfInterlaced.lean#L135-L156

import Mathlib
import Definitions.Def_Formalism_GradedWeylDivisibility_StatementE
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_LowerTriOfInterlaced
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial Formalism.GradedWeylDivisibility
noncomputable section
open GlobalTheory GlobalTheory.FockHighestWeight
variable {r n : ℕ}

theorem GlobalTheory.FockHighestWeight.component_eq_smul_hw {R : Type} [CommRing R] [IsDomain R] (hn : n ≤ r) {ν : Fin n → ℕ} (hν : Antitone ν)
    {F : MvPolynomial (Fin r × Fin n) R} (hF : F ∈ dualWeyl R r n ν) :
    weightedHomogeneousComponent (rowW r n) (rowNu (r := r) ν) F = eval (idFrame R r n) F • hw R hn ν := by sorry
