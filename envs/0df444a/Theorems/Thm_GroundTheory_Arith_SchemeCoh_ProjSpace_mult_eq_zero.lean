-- Prove2me | Theorems.Thm_GroundTheory_Arith_SchemeCoh_ProjSpace_mult_eq_zero
-- name    : GroundTheory.Arith.SchemeCoh.ProjSpace.mult_eq_zero
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T23:28:11.649112+00:00
-- url     : https://prove2.me/theorems/56d5c22c-f9ee-4b55-b1ef-71c59052356e
-- title:
--   Proj Space: mult eq zero
-- statement:
--   The Proj Space construction uses the mult eq zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/SchemeCohomology/ProjLaurent.lean#L60-L64
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/SchemeCohomology/ProjLaurent.lean#L60-L64

import Mathlib
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_ProjSpace
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_ProjLaurent
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
open AlgebraicGeometry MvPolynomial
universe u
attribute [local instance] MvPolynomial.gradedAlgebra
noncomputable section
open GroundTheory.Arith.SchemeCoh.ProjSpace
variable {A : Type u} [CommRing A] {n : ℕ}

theorem GroundTheory.Arith.SchemeCoh.ProjSpace.mult_eq_zero {p : ℕ} (i : Fin p → Fin (n + 1)) {j : Fin (n + 1)} (hj : j ∉ Set.range i) :
    mult i j = 0 := by sorry
