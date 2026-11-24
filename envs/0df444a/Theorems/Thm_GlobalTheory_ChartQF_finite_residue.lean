-- Prove2me | Theorems.Thm_GlobalTheory_ChartQF_finite_residue
-- name    : GlobalTheory.ChartQF.finite_residue
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T11:08:54.661713+00:00
-- url     : https://prove2.me/theorems/95dbb793-6ddd-48f2-8ad4-3839d68f045c
-- title:
--   Chart QF: finite residue
-- statement:
--   The Chart QF construction uses the finite residue property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/IsAlgebraicOfMemClosure.lean#L32-L83
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/IsAlgebraicOfMemClosure.lean#L32-L83

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsCompletedStrictHens
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsAlgebraicOfMemClosure
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory IsLocalRing
open ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ChartQF
variable {A R : Type} [CommRing A] [CommRing R] [IsLocalRing A] [IsLocalRing R] (f : A →+* R)

theorem GlobalTheory.ChartQF.finite_residue [IsLocalHom f] {K : Type} [Field K] [Algebra (ResidueField A) K] (ev : R →+* K)
    (hk : RingHom.ker ev = maximalIdeal R)
    (hev : ∀ a, ev (f a) = algebraMap (ResidueField A) K (residue A a)) {T : Set R} {G : Finset R}
    (hT : T ⊆ Set.range f)
    (hb : ∀ r : R, ∃ a ∈ Subring.closure (T ∪ (G : Set R)), ∃ b ∈ Subring.closure (T ∪ (G : Set R)),
      b ∉ maximalIdeal R ∧ b * r - a ∈ maximalIdeal R)
    (hG : ∀ g ∈ G, IsAlgebraic (ResidueField A) (ev g)) : ((residue R).comp f).Finite := by sorry
