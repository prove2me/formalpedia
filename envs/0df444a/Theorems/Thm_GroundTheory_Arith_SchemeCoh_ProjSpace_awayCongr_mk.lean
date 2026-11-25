-- Prove2me | Theorems.Thm_GroundTheory_Arith_SchemeCoh_ProjSpace_awayCongr_mk
-- name    : GroundTheory.Arith.SchemeCoh.ProjSpace.awayCongr_mk
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T05:17:13.663849+00:00
-- url     : https://prove2.me/theorems/e06c9daf-5beb-4b10-9b3a-3bdd83268fec
-- title:
--   Proj Space: away Congr mk
-- statement:
--   The Proj Space construction uses the away Congr mk property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/SchemeCohomology/ProperCohomology/ProjBaseChange.lean#L73-L78
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/SchemeCohomology/ProperCohomology/ProjBaseChange.lean#L73-L78

import Mathlib
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_ProjectiveSpaceChart
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_ProjectiveCohomology_TwistingSheaf
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_ProperCohomology_ProjBaseChange
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Arith GroundTheory.Arith.SchemeCoh
open AlgebraicGeometry CategoryTheory Limits MvPolynomial HomogeneousLocalization
universe u
attribute [local instance] MvPolynomial.gradedAlgebra
noncomputable section
open GroundTheory.Arith.SchemeCoh.ProjSpace
variable (A B : Type u) [CommRing A] [CommRing B] [Algebra A B] (n : ℕ)

theorem GroundTheory.Arith.SchemeCoh.ProjSpace.awayCongr_mk {s t : MvPolynomial (Fin (n + 1)) B} (h : s = t) {d : ℕ}
    (hs : s ∈ grading B n d) (ht : t ∈ grading B n d) (m : ℕ) (x : MvPolynomial (Fin (n + 1)) B)
    (hx : x ∈ grading B n (m • d)) :
    awayCongr B n h (Away.mk (grading B n) hs m x hx) = Away.mk (grading B n) ht m x hx := by sorry
