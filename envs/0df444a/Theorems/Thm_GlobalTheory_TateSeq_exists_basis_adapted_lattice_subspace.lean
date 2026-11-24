-- Prove2me | Theorems.Thm_GlobalTheory_TateSeq_exists_basis_adapted_lattice_subspace
-- name    : GlobalTheory.TateSeq.exists_basis_adapted_lattice_subspace
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T21:02:45.991896+00:00
-- url     : https://prove2.me/theorems/01e8f464-6198-4c2e-ad47-76e52f5dddb9
-- title:
--   Tate Seq: exists basis adapted lattice subspace
-- statement:
--   The Tate Seq construction uses the exists basis adapted lattice subspace property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/ExistsBasisAdaptedLatticeSubspace.lean#L71-L99
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/ExistsBasisAdaptedLatticeSubspace.lean#L71-L99

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

theorem GlobalTheory.TateSeq.exists_basis_adapted_lattice_subspace (l r : ℕ) [Fact l.Prime] (V : Type) [AddCommGroup V]
    [Module (ZMod l) V] (hc : Nat.card V = l ^ r) :
    ∃ b : Fin r → V,
      (∀ a : Fin r → ℤ, ∑ i, a i • b i = 0 → ∀ i, (l : ℤ) ∣ a i) ∧
      (∀ y : V, ∃ a : Fin r → ℤ, ∑ i, a i • b i = y) := by sorry
