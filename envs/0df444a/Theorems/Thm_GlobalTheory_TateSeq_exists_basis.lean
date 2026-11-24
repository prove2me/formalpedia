-- Prove2me | Theorems.Thm_GlobalTheory_TateSeq_exists_basis
-- name    : GlobalTheory.TateSeq.exists_basis
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T21:02:39.400741+00:00
-- url     : https://prove2.me/theorems/4cfe941b-4291-4384-b3b9-909fd2c4f0df
-- title:
--   Tate Seq: exists basis
-- statement:
--   The Tate Seq construction uses the exists basis property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/ExistsBasisAdaptedLatticeSubspace.lean#L101-L115
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/ExistsBasisAdaptedLatticeSubspace.lean#L101-L115

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

theorem GlobalTheory.TateSeq.exists_basis (l r : ℕ) [Fact l.Prime]
    (h : Nat.card {x : M // l • x = 0} = l ^ r) :
    ∃ b : Fin r → M, (∀ i, l • b i = 0) ∧
      (∀ a : Fin r → ℤ, ∑ i, a i • b i = 0 → ∀ i, (l : ℤ) ∣ a i) ∧
      (∀ y : M, l • y = 0 → ∃ a : Fin r → ℤ, ∑ i, a i • b i = y) := by sorry
