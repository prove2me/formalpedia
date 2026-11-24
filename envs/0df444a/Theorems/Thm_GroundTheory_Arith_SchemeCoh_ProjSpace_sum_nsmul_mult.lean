-- Prove2me | Theorems.Thm_GroundTheory_Arith_SchemeCoh_ProjSpace_sum_nsmul_mult
-- name    : GroundTheory.Arith.SchemeCoh.ProjSpace.sum_nsmul_mult
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T23:28:16.258278+00:00
-- url     : https://prove2.me/theorems/8955234d-32ae-4382-b50c-8106bcbe67fc
-- title:
--   Proj Space: sum nsmul mult
-- statement:
--   The Proj Space construction uses the sum nsmul mult property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/SchemeCohomology/ProjLaurent.lean#L77-L80
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/SchemeCohomology/ProjLaurent.lean#L77-L80

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

theorem GroundTheory.Arith.SchemeCoh.ProjSpace.sum_nsmul_mult {p : ℕ} (i : Fin p → Fin (n + 1)) (N : ℕ) :
    ∑ x, (N • mult i) x = (N : ℤ) * p := by sorry
