-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_Spherical_isIntegral_of_forall
-- name    : GroundTheory.Automorphic.Spherical.isIntegral_of_forall
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T23:33:57.673722+00:00
-- url     : https://prove2.me/theorems/fd42ad96-8b9a-4cd8-ab61-eaa60831c2c9
-- title:
--   Spherical: is Integral of forall
-- statement:
--   The Spherical construction uses the is Integral of forall property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/SphericalLaurent.lean#L147-L185
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/SphericalLaurent.lean#L147-L185

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_SphericalLaurent
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GroundTheory GroundTheory.Automorphic
open GroundTheory.Automorphic.Spherical
open AddMonoidAlgebra
variable {n : ℕ}

theorem GroundTheory.Automorphic.Spherical.isIntegral_of_forall (A : Subalgebra ℂ (LaurentRing n))
    (h₁ : ∀ i, IsIntegral A (monomial (Pi.single i 1 : Fin n → ℤ)))
    (h₂ : ∀ i, IsIntegral A (monomial (Pi.single i (-1) : Fin n → ℤ))) :
    Algebra.IsIntegral A (LaurentRing n) := by sorry
