-- Prove2me | Theorems.Thm_GroundTheory_Arith_SchemeCoh_ProjSpace_mult_apply
-- name    : GroundTheory.Arith.SchemeCoh.ProjSpace.mult_apply
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T18:39:04.65932+00:00
-- url     : https://prove2.me/theorems/6fa41252-5c7e-45ac-91cd-2acbf9a763c7
-- title:
--   Proj Space: mult apply
-- statement:
--   The Proj Space construction uses the mult apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/SchemeCohomology/ProjLaurent.lean#L56-L58
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/SchemeCohomology/ProjLaurent.lean#L56-L58

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

theorem GroundTheory.Arith.SchemeCoh.ProjSpace.mult_apply {p : ℕ} (i : Fin p → Fin (n + 1)) (j : Fin (n + 1)) :
    mult i j = ((Finset.univ.filter fun a => i a = j).card : ℤ) := by sorry
