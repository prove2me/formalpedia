-- Prove2me | Theorems.Thm_GlobalTheory_residue_atMaximal_finite_formallyUnramified
-- name    : GlobalTheory.residue_atMaximal_finite_formallyUnramified
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T16:45:31.25241+00:00
-- url     : https://prove2.me/theorems/bb094f81-3206-4aec-be53-c66688b744c7
-- title:
--   Global Theory: residue at Maximal finite formally Unramified
-- statement:
--   The Global Theory construction uses the residue at Maximal finite formally Unramified property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/LocalizationResidueFiniteUnram.lean#L15-L39
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/LocalizationResidueFiniteUnram.lean#L15-L39

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_LocalizationResidueFiniteUnram
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open IsLocalRing TensorProduct
open GlobalTheory

theorem GlobalTheory.residue_atMaximal_finite_formallyUnramified :
    ∀ (B S : Type) [CommRing B] [CommRing S] [Algebra B S] (J q : Ideal S) [q.IsMaximal], J ≤ q → Algebra.FormallyUnramified B (S ⧸ J) → Module.Finite B (S ⧸ J) → ((IsLocalRing.residue (Localization.AtPrime q)).comp ((algebraMap S (Localization.AtPrime q)).comp (algebraMap B S))).Finite ∧ ((IsLocalRing.residue (Localization.AtPrime q)).comp ((algebraMap S (Localization.AtPrime q)).comp (algebraMap B S))).FormallyUnramified := by sorry
