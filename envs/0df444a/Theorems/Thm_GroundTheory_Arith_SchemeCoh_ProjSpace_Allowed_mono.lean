-- Prove2me | Theorems.Thm_GroundTheory_Arith_SchemeCoh_ProjSpace_Allowed_mono
-- name    : GroundTheory.Arith.SchemeCoh.ProjSpace.Allowed.mono
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T23:27:55.989738+00:00
-- url     : https://prove2.me/theorems/5fe83f48-dc26-499a-94be-bbb0c4fdc3d5
-- title:
--   Allowed: mono
-- statement:
--   The Allowed construction uses the mono property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/SchemeCohomology/ProjLaurent.lean#L154-L156
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/SchemeCohomology/ProjLaurent.lean#L154-L156

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

theorem GroundTheory.Arith.SchemeCoh.ProjSpace.Allowed.mono {s t : Set (Fin (n + 1))} {k : ℤ} {m : Fin (n + 1) → ℤ} (h : Allowed s k m)
    (hst : s ⊆ t) : Allowed t k m := by sorry
