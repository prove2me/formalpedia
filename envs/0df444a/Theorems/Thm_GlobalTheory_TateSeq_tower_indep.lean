-- Prove2me | Theorems.Thm_GlobalTheory_TateSeq_tower_indep
-- name    : GlobalTheory.TateSeq.tower_indep
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T21:02:40.168816+00:00
-- url     : https://prove2.me/theorems/9fbc4506-ab64-4aad-a023-872fdad98285
-- title:
--   Tate Seq: tower indep
-- statement:
--   The Tate Seq construction uses the tower indep property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/ExistsBasisAdaptedLatticeSubspace.lean#L137-L157
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/ExistsBasisAdaptedLatticeSubspace.lean#L137-L157

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_OfDerivationFnOn
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_PlOrdSomeOfAssociated
import Definitions.Def_Development_AbelianVarietyTheory_Statements_SemistableTorsion_SemistableFin
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsBasisAdaptedLatticeSubspace
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.TateSeq
variable {M : Type} [AddCommGroup M]

theorem GlobalTheory.TateSeq.tower_indep {l r : ℕ} {e : ℕ → Fin r → M} (he : ∀ n i, l • e (n + 1) i = e n i)
    (h1 : ∀ a : Fin r → ℤ, ∑ i, a i • e 1 i = 0 → ∀ i, (l : ℤ) ∣ a i) (n : ℕ) :
    ∀ a : Fin r → ℤ, ∑ i, a i • e n i = 0 → ∀ i, (l : ℤ) ^ n ∣ a i := by sorry
