-- Prove2me | Theorems.Thm_GlobalTheory_T_principalGroup_acts_freely_on_flags
-- name    : GlobalTheory.T.principalGroup_acts_freely_on_flags
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T20:55:28.837727+00:00
-- url     : https://prove2.me/theorems/81e40f2b-5c56-4a4e-8b6f-f34e9847c335
-- title:
--   T: principal Group acts freely on flags
-- statement:
--   The T construction uses the principal Group acts freely on flags property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/PrincipalGroupActsFreelyOnFlagsStatement.lean#L16-L17
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/PrincipalGroupActsFreelyOnFlagsStatement.lean#L16-L17

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_PrincipalGroupActsFreelyOnFlags
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ExistenceOfLattices_UnivFrame
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ExistenceOfLattices_NormConst
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_CuspFree
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_RdOrbIntOfLatZ
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_AllTest
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FundamentalDomainPointBound
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Landherr__ExistsNormTensor_9eff20d6b37353d0
import Definitions.Def_Development_AbelianVarietyTheory_Statements_HyperbolicHypotheses_HypothesesInhabitedHyperbolic
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_PrincipalGroupActsFreelyOnFlagsStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.L2.PjFree
open AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Frames GlobalTheory.FrameUnif
open scoped Matrix nonZeroDivisors
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.principalGroup_acts_freely_on_flags : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (l : Level H) (Di : Datum H) (r : ℕ) (ξ₀ : E) (Gm : Matrix (Fin r) (Fin r) E) (φ0 : Di.La →ₗ[𝓞 E] (Fin r → E)), cc ξ₀ = -ξ₀ → (Function.Injective φ0 ∧ Submodule.span E (Set.range φ0) = ⊤ ∧ (∀ a b, cc (Gm a b) = Gm b a) ∧ Gm.det ≠ 0 ∧ ∀ x y, ((Di.EF x y : ℤ) : ℚ) = Algebra.trace ℚ E (-ξ₀ * herm Gm (φ0 x) (φ0 y))) → ∀ (Ψ : Finset (E →+* ℂ)) (q : ℕ), (∀ τ, τ ∈ Ψ ↔ τ (H.rt : E) = H.rt0) → ∀ γ ∈ princ l Gm Di φ0, ∀ x ∈ GG Ψ Gm q, ∀ b ∈ Bor Ψ r, lact γ x = rmul x b → γ = 1 := by sorry
