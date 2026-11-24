-- Prove2me | Theorems.Thm_GlobalTheory_HalfPairing_halves_free_and_adjoint
-- name    : GlobalTheory.HalfPairing.halves_free_and_adjoint
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T14:03:22.466727+00:00
-- url     : https://prove2.me/theorems/434d7383-abf3-4de0-be29-0aeaf22bbeff
-- title:
--   Half Pairing: halves free and adjoint
-- statement:
--   The Half Pairing construction uses the halves free and adjoint property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/HalvesFreeAndAdjoint.lean#L279-L303
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/HalvesFreeAndAdjoint.lean#L279-L303

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_NormsFree
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_RegPFree
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_RegQFree
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_ThShort
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_LiftLaSpec
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_IsGenFrGenFr
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_ChartDirectionsIntegral
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_AllTest
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_Development_AbelianVarietyTheory_Counterexamples_LevelGroupExamples_ZeroNotAdmissibleOfRankPos
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_HalvesFreeAndAdjoint
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.HalfPairing
open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj

theorem GlobalTheory.HalfPairing.halves_free_and_adjoint : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), ∀ (n : ℕ) (d : DeltaDat Xo c n), d.IsLev → (∃ x₀ : Fin (Dw.p + Dw.q) → LaJ Xo c d, Submodule.span (𝓞 E) (Set.range x₀) = ⊤) ∧ (∀ x x' : Fin (Dw.p + Dw.q) → LaJ Xo c d, Submodule.span (𝓞 E) (Set.range x) = ⊤ → Submodule.span (𝓞 E) (Set.range x') = ⊤ → ∃! g : LaJ Xo c d ≃ₗ[𝓞 E] LaJ Xo c d, ∀ b, g (x b) = x' b) ∧ ∃ adj : (LaJ Xo c d ≃ₗ[𝓞 E] LaJ Xo c d) → (LaI Xo c d ≃ₗ[𝓞 E] LaI Xo c d), (∀ g g', adj (g * g') = adj g' * adj g) ∧ ∀ (k : LaI Xo c d ≃ₗ[𝓞 E] LaI Xo c d) (kst : LaJ Xo c d ≃ₗ[𝓞 E] LaJ Xo c d), (∀ u v : Dw.La, ((d.pd : ℤ) ∣ Dw.EF (qRep (kst (Submodule.Quotient.mk u))) (cHalf H d.I • v) - Dw.EF u (cHalf H d.I • qRep (k (Submodule.Quotient.mk v))))) ↔ k = adj kst := by sorry
