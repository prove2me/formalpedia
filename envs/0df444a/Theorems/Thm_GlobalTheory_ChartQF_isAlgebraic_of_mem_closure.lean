-- Prove2me | Theorems.Thm_GlobalTheory_ChartQF_isAlgebraic_of_mem_closure
-- name    : GlobalTheory.ChartQF.isAlgebraic_of_mem_closure
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T11:08:52.925585+00:00
-- url     : https://prove2.me/theorems/9ec20fa6-3ff7-4f1f-a788-379d1fcaeec4
-- title:
--   Chart QF: is Algebraic of mem closure
-- statement:
--   The Chart QF construction uses the is Algebraic of mem closure property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/IsAlgebraicOfMemClosure.lean#L15-L30
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/IsAlgebraicOfMemClosure.lean#L15-L30

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

theorem GlobalTheory.ChartQF.isAlgebraic_of_mem_closure {K : Type} [Field K] [Algebra (ResidueField A) K] (ev : R →+* K)
    (hev : ∀ a, ev (f a) = algebraMap (ResidueField A) K (residue A a)) {T G : Set R} (hT : T ⊆ Set.range f)
    {D : Subalgebra (ResidueField A) K} (hG : ∀ g ∈ G, ev g ∈ D) {b : R} (hb : b ∈ Subring.closure (T ∪ G)) :
    ev b ∈ D := by sorry
