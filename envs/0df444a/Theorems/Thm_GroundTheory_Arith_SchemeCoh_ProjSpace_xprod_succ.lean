-- Prove2me | Theorems.Thm_GroundTheory_Arith_SchemeCoh_ProjSpace_xprod_succ
-- name    : GroundTheory.Arith.SchemeCoh.ProjSpace.xprod_succ
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T23:27:57.429739+00:00
-- url     : https://prove2.me/theorems/fef5c303-e4b6-4a46-84d9-4379d916a674
-- title:
--   Proj Space: xprod succ
-- statement:
--   The Proj Space construction uses the xprod succ property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/SchemeCohomology/ProjSpace.lean#L46-L48
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/SchemeCohomology/ProjSpace.lean#L46-L48

import Mathlib
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_ProjTwistAway
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_ConsCompSuccAboveZero
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_ProjSpace
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
open AlgebraicGeometry TopologicalSpace CategoryTheory Opposite MvPolynomial
universe u
attribute [local instance] MvPolynomial.gradedAlgebra
noncomputable section
open ProjSpace
open GroundTheory.Arith.SchemeCoh.ProjSpace
variable {A : Type u} [CommRing A] {n : ℕ}

theorem GroundTheory.Arith.SchemeCoh.ProjSpace.xprod_succ {p : ℕ} (i : Fin (p + 1) → Fin (n + 1)) :
    xprod (A := A) i = X (i 0) * xprod (A := A) (i ∘ Fin.succ) := by sorry
