-- Prove2me | Theorems.Thm_GroundTheory_Arith_SchemeCoh_ProjSpace_awayCongr_symm
-- name    : GroundTheory.Arith.SchemeCoh.ProjSpace.awayCongr_symm
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T04:28:50.904855+00:00
-- url     : https://prove2.me/theorems/959b1cfc-8143-512b-8034-60566da27a98
-- title:
--   Proj Space: away Congr symm
-- statement:
--   The Proj Space construction uses the away Congr symm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/SchemeCohomology/ProperCohomology/ProjBaseChange.lean#L97-L100
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/SchemeCohomology/ProperCohomology/ProjBaseChange.lean#L97-L100

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
variable {A B n}

theorem GroundTheory.Arith.SchemeCoh.ProjSpace.awayCongr_symm {s t : MvPolynomial (Fin (n + 1)) B} (h : s = t) :
    (awayCongr B n h).symm = awayCongr B n h.symm := by sorry
