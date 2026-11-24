-- Prove2me | Theorems.Thm_GroundTheory_Arith_SchemeCoh_ProjSpace_LDeg_mono
-- name    : GroundTheory.Arith.SchemeCoh.ProjSpace.LDeg_mono
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T18:39:57.426313+00:00
-- url     : https://prove2.me/theorems/a5cbe9a4-38e7-4f03-b9cb-67c75a3227da
-- title:
--   Proj Space: LDeg mono
-- statement:
--   The Proj Space construction uses the LDeg mono property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/SchemeCohomology/ProjLaurent.lean#L170-L171
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/SchemeCohomology/ProjLaurent.lean#L170-L171

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

theorem GroundTheory.Arith.SchemeCoh.ProjSpace.LDeg_mono {s t : Set (Fin (n + 1))} (hst : s ⊆ t) (k : ℤ) : LDeg A s k ≤ LDeg A t k := by sorry
