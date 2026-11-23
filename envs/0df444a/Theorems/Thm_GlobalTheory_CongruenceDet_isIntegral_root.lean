-- Prove2me | Theorems.Thm_GlobalTheory_CongruenceDet_isIntegral_root
-- name    : GlobalTheory.CongruenceDet.isIntegral_root
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T11:37:45.525187+00:00
-- url     : https://prove2.me/theorems/8735ba17-f2b2-424d-84e3-75325dba8215
-- title:
--   Congruence Det: is Integral root
-- statement:
--   The Congruence Det construction uses the is Integral root property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/IsIntegralDetSubOne.lean#L13-L71
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/IsIntegralDetSubOne.lean#L13-L71

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_Signature
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_IsIntegralDetSubOne
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Matrix
open scoped nonZeroDivisors
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CongruenceDet
open NumberField Matrix
open scoped nonZeroDivisors

theorem GlobalTheory.CongruenceDet.isIntegral_root {R E K : Type} [CommRing R] [Field E]
    [Field K] [CharZero K]
    [Algebra R E] [Algebra R K] [Algebra E K] [IsScalarTower R E K] {r M : ℕ} (hM : M ≠ 0)
    (Λ : Submodule R (Fin r → E)) (g : Matrix (Fin r) (Fin r) E) (hfg : Λ.FG)
    (hspan : Submodule.span E (Λ : Set (Fin r → E)) = ⊤)
    (hg : ∀ v ∈ Λ, ∃ w ∈ Λ, g *ᵥ v = v + M • w) (μ : K)
    (hμ : (g.map (algebraMap E K)).charpoly.IsRoot μ) :
    IsIntegral R ((μ - 1) / M) := by sorry
