-- Prove2me | Theorems.Thm_GlobalTheory_InertiaMovesRoot_exists_cong_of_cong_on_fixed
-- name    : GlobalTheory.InertiaMovesRoot.exists_cong_of_cong_on_fixed
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T17:01:58.976158+00:00
-- url     : https://prove2.me/theorems/8613fd68-f80b-452a-b988-ed376caee612
-- title:
--   Inertia Moves Root: exists cong of cong on fixed
-- statement:
--   The Inertia Moves Root construction uses the exists cong of cong on fixed property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/ExistsCongOfCongOnFixed.lean#L171-L210
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/ExistsCongOfCongOnFixed.lean#L171-L210

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AutomorphicMembership_MonodromyZeroOfWeilDeligneRepClassIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_ExistsCongOfCongOnFixed
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial Module GlobalTheory.WeilDeligne Pointwise
open GlobalTheory GlobalTheory.InertiaMovesRoot
variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
  {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)}

theorem GlobalTheory.InertiaMovesRoot.exists_cong_of_cong_on_fixed {R S G : Type} [CommRing R] [CommRing S] [Algebra R S]
    [Group G] [MulSemiringAction G S] [SMulCommClass G R S] [TopologicalSpace G]
    [IsTopologicalGroup G] [TopologicalSpace S] [DiscreteTopology S] [ContinuousSMul G S]
    (H : Subgroup G) [CompactSpace H] [TotallyDisconnectedSpace H] (Q : Ideal S) [Q.IsPrime]
    (g : G) (hg : ∀ b : S, (∀ k ∈ H, k • b = b) → g • b - b ∈ Q) :
    ∃ k ∈ H, ∃ k' ∈ H, ∀ b : S, (k' * g * k) • b - b ∈ Q := by sorry
