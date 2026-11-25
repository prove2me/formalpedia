-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_hasFiniteLength_of_coinvariants
-- name    : GroundTheory.Automorphic.hasFiniteLength_of_coinvariants
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T11:55:01.068701+00:00
-- url     : https://prove2.me/theorems/1d723a96-802f-5315-a01b-2b0a917cd201
-- title:
--   Automorphic: has Finite Length of coinvariants
-- statement:
--   The Automorphic construction uses the has Finite Length of coinvariants property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/FiniteLengthSubquotient.lean#L252-L356
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/FiniteLengthSubquotient.lean#L252-L356

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_FiniteLengthLattice
import Definitions.Def_GroundTheory_AutomorphicForms_JacquetAdmissible
import Definitions.Def_GroundTheory_AutomorphicForms_FiniteLengthSubquotient
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.Automorphic
open Function Parabolic
universe u
variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

theorem GroundTheory.Automorphic.hasFiniteLength_of_coinvariants {V : Type u} [AddCommGroup V] [Module ℂ V]
    {X : Representation ℂ G V} (hX : IsSmooth X) {ι : Type*} [Finite ι] (N : ι → Subgroup G)
    [∀ i, LocallyCompactSpace (N i)] [∀ i, T2Space (N i)] [∀ i, TotallyDisconnectedSpace (N i)]
    (hN : ∀ i (s : Finset (N i)), ∃ K : Subgroup (N i), IsCompact (K : Set (N i)) ∧
      IsOpen (K : Set (N i)) ∧ ∀ x ∈ s, x ∈ K)
    {M : ι → Type*} [∀ i, Group (M i)]
    (τ : ∀ i, Representation ℂ (M i) (Representation.Coinvariants (X.comp (N i).subtype)))
    (hτ : ∀ i m, ∃ g : G, ∃ c : ℂ, ∀ v, τ i m (Representation.Coinvariants.mk _ v) =
      c • Representation.Coinvariants.mk _ (X g v))
    (hfin : ∀ i, HasFiniteLength (τ i))
    (hfaith : ∀ (W : Type u) [AddCommGroup W] [Module ℂ W] (π : Representation ℂ G W)
      [π.IsIrreducible], IsSmooth π → IsSubquotient π X →
        ∃ i, Nontrivial (Representation.Coinvariants (π.comp (N i).subtype))) :
    HasFiniteLength X := by sorry
