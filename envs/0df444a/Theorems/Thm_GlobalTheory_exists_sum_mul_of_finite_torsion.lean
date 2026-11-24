-- Prove2me | Theorems.Thm_GlobalTheory_exists_sum_mul_of_finite_torsion
-- name    : GlobalTheory.exists_sum_mul_of_finite_torsion
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T22:42:28.384354+00:00
-- url     : https://prove2.me/theorems/44c0a085-de55-479b-8577-6a96edb4c3f3
-- title:
--   Global Theory: exists sum mul of finite torsion
-- statement:
--   The Global Theory construction uses the exists sum mul of finite torsion property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/InvCupPairingOfInvCupCharacters.lean#L18-L42
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/InvCupPairingOfInvCupCharacters.lean#L18-L42

import Mathlib
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_GaloisCohomology__PoitouTateNineTermTransgressionZeroApply_433ca0b5d42a991a
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_GaloisCohomology__ContinuousCycMod_abd9886c27059cc0
import Definitions.Def_Formalism_GaloisCohomology_Statement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_InvCupPairingOfInvCupCharacters
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.Published GlobalTheory.Published.PoitouTate
open GlobalTheory

theorem GlobalTheory.exists_sum_mul_of_finite_torsion (l : ℕ) [Fact l.Prime] (M M' : Type) [AddCommGroup M]
    [AddCommGroup M'] [Module (ZMod l) M] (β : M →+ M' →+ ZMod l) (S : Set M)
    (hS : S.Finite) :
    ∃ (ι : Type) (s : Finset ι) (c : ι → M →+ ZMod l) (d : ι → M' →+ ZMod l),
      ∀ m ∈ S, ∀ m' : M', β m m' = ∑ k ∈ s, c k m * d k m' := by sorry
