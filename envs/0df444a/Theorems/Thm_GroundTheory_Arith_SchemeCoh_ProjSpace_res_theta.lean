-- Prove2me | Theorems.Thm_GroundTheory_Arith_SchemeCoh_ProjSpace_res_theta
-- name    : GroundTheory.Arith.SchemeCoh.ProjSpace.res_theta
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T00:11:31.844035+00:00
-- url     : https://prove2.me/theorems/34048e49-d950-424e-b795-a5fc1624c25e
-- title:
--   Proj Space: res theta
-- statement:
--   The Proj Space construction uses the res theta property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/SchemeCohomology/ProjCechModel.lean#L75-L85
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/SchemeCohomology/ProjCechModel.lean#L75-L85

import Mathlib
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_ProjLaurent
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_CechSeparated
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_ProjCechModel
import Theorems.Thm_GroundTheory_Arith_SchemeCoh_ProjSpace_LDeg_mono

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
open GroundTheory.Arith.SchemeCoh.ProjSpace
variable {A : Type u} [CommRing A] {n : ℕ}

theorem GroundTheory.Arith.SchemeCoh.ProjSpace.res_theta {p q : ℕ} {i : Fin (p + 1) → Fin (n + 1)} {i' : Fin (q + 1) → Fin (n + 1)}
    (h : Set.range i ⊆ Set.range i') (hle : inter (cover A n) i' ≤ inter (cover A n) i) (k : ℤ)
    (ℓ : LDeg A (Set.range i) k) :
    res (twistAb A n k) hle (theta i k ℓ) = theta i' k ⟨ℓ.1, LDeg_mono h k ℓ.2⟩ := by sorry
