-- Prove2me | Theorems.Thm_GroundTheory_Arith_SchemeCoh_ProjSpace_sum_mult
-- name    : GroundTheory.Arith.SchemeCoh.ProjSpace.sum_mult
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T23:27:51.457948+00:00
-- url     : https://prove2.me/theorems/c5b76cf2-8f53-4fad-a8cb-4cd6d275113e
-- title:
--   Proj Space: sum mult
-- statement:
--   The Proj Space construction uses the sum mult property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/SchemeCohomology/ProjLaurent.lean#L72-L75
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/SchemeCohomology/ProjLaurent.lean#L72-L75

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

theorem GroundTheory.Arith.SchemeCoh.ProjSpace.sum_mult {p : ℕ} (i : Fin p → Fin (n + 1)) : ∑ j, mult i j = p := by sorry
