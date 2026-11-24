-- Prove2me | Theorems.Thm_GroundTheory_Arith_SchemeCoh_ProjSpace_mem_LDeg_iff
-- name    : GroundTheory.Arith.SchemeCoh.ProjSpace.mem_LDeg_iff
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T23:28:08.679808+00:00
-- url     : https://prove2.me/theorems/b9757379-ee54-4732-93ea-7b347cfd8fca
-- title:
--   Proj Space: mem LDeg iff
-- statement:
--   The Proj Space construction uses the mem LDeg iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/SchemeCohomology/ProjLaurent.lean#L190-L256
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/SchemeCohomology/ProjLaurent.lean#L190-L256

import Mathlib
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_ProjSpace
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_ProjLaurent
import Theorems.Thm_GroundTheory_Arith_SchemeCoh_ProjSpace_xprod_mem

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

theorem GroundTheory.Arith.SchemeCoh.ProjSpace.mem_LDeg_iff {p : ℕ} (i : Fin (p + 1) → Fin (n + 1)) (k : ℤ) (ℓ : Laurent A n) :
    ℓ ∈ LDeg A (Set.range i) k ↔
      ∃ z ∈ ProjTwist.awayDeg (grading A n) (xprod_mem i) (Nat.succ_pos p) k,
        awayToLaurent i z = ℓ := by sorry
