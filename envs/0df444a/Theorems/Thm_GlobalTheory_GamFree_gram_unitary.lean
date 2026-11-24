-- Prove2me | Theorems.Thm_GlobalTheory_GamFree_gram_unitary
-- name    : GlobalTheory.GamFree.gram_unitary
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T13:49:20.996842+00:00
-- url     : https://prove2.me/theorems/6cbd9b09-c852-43ff-a5bd-606636d2eb74
-- title:
--   Gam Free: gram unitary
-- statement:
--   The Gam Free construction uses the gram unitary property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/IsOfFinOrderOfBounded.lean#L28-L41
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/IsOfFinOrderOfBounded.lean#L28-L41

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_Signature
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_ProdCastLESucc
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_ExistsIntMulIntegral
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_BoundedPowOfTriangularIsometry
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_IsOfFinOrderOfBounded
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Matrix
open scoped nonZeroDivisors ComplexConjugate
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.GamFree
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

theorem GlobalTheory.GamFree.gram_unitary (G γ : Matrix (Fin r) (Fin r) E)
    (hγ : ∀ x y, FD.herm G (γ *ᵥ x) (γ *ᵥ y) = FD.herm G x y) (τ : E →+* ℂ)
    (Y : Matrix (Fin r) (Fin r) ℂ) : FD.gram τ G (γ.map τ * Y) = FD.gram τ G Y := by sorry
