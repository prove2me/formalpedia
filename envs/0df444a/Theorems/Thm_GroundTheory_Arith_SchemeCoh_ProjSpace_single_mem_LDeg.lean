-- Prove2me | Theorems.Thm_GroundTheory_Arith_SchemeCoh_ProjSpace_single_mem_LDeg
-- name    : GroundTheory.Arith.SchemeCoh.ProjSpace.single_mem_LDeg
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T18:40:17.471217+00:00
-- url     : https://prove2.me/theorems/1815732a-b1da-4e4c-b766-452c53c839be
-- title:
--   Proj Space: single mem LDeg
-- statement:
--   The Proj Space construction uses the single mem LDeg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/SchemeCohomology/ProjLaurent.lean#L173-L180
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/SchemeCohomology/ProjLaurent.lean#L173-L180

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

theorem GroundTheory.Arith.SchemeCoh.ProjSpace.single_mem_LDeg {s : Set (Fin (n + 1))} {k : ℤ} {m : Fin (n + 1) → ℤ} (hm : Allowed s k m)
    (c : A) : AddMonoidAlgebra.single m c ∈ LDeg A s k := by sorry
