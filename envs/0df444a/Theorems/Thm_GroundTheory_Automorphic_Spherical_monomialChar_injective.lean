-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_Spherical_monomialChar_injective
-- name    : GroundTheory.Automorphic.Spherical.monomialChar_injective
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T23:34:00.357885+00:00
-- url     : https://prove2.me/theorems/41b5f3cc-1a52-4916-b2ed-a8567311332c
-- title:
--   Spherical: monomial Char injective
-- statement:
--   The Spherical construction uses the monomial Char injective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/SphericalLaurent.lean#L56-L67
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/SphericalLaurent.lean#L56-L67

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

theorem GroundTheory.Automorphic.Spherical.monomialChar_injective : Function.Injective (monomialChar : (Fin n → ℤ) → _) := by sorry
