-- Prove2me | Theorems.Thm_GroundTheory_LocalField_coeff_injective
-- name    : GroundTheory.LocalField.coeff_injective
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T07:16:41.168056+00:00
-- url     : https://prove2.me/theorems/18dcc16c-806f-44c6-923d-0cfcaf41b6cc
-- title:
--   Local Field: coeff injective
-- statement:
--   The Local Field construction uses the coeff injective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/NormalLattice.lean#L41-L47
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/NormalLattice.lean#L41-L47

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_Interface
import Definitions.Def_GroundTheory_LocalFields_UnitsBasic
import Definitions.Def_GroundTheory_LocalFields_NormalLattice
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GroundTheory GroundTheory.LocalField
open ValuativeRel Finset
variable {K L : Type*} [Field K] [ValuativeRel K] [Field L] [Algebra K L]
variable [FiniteDimensional K L]
variable (π : 𝒪[K]) (θ : L)

theorem GroundTheory.LocalField.coeff_injective (hθ : LinearIndependent K fun σ : Gal(L/K) => σ θ)
    {c d : Gal(L/K) → 𝒪[K]} (h : ∑ σ, c σ • σ θ = ∑ σ, d σ • σ θ) : c = d := by sorry
