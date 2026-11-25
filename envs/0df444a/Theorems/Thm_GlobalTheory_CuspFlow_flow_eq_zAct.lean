-- Prove2me | Theorems.Thm_GlobalTheory_CuspFlow_flow_eq_zAct
-- name    : GlobalTheory.CuspFlow.flow_eq_zAct
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T02:40:13.154723+00:00
-- url     : https://prove2.me/theorems/07b6e4d2-9ddb-5388-9aab-4fcf9a5454d8
-- title:
--   Cusp Flow: flow eq z Act
-- statement:
--   The Cusp Flow construction uses the flow eq z Act property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaShiftProofs/CuspFlowEqTorusAction.lean#L125-L164
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaShiftProofs/CuspFlowEqTorusAction.lean#L125-L164

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_ArchimedeanQuadraticData_MaximalCuspKernels_MaxCuspsSt
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_ArchimedeanQuadraticData_MaximalCuspKernels_MaxCuspsPfA
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_ArchimedeanQuadraticData_MaximalCuspKernels_MaxCuspsPfB
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_RdOrbIntOfLatZ
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_CuspFlowEqTorusAction
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
open ReciprocityTheory.ChartRestriction.G.FD NumberField Formalism.L2.Pj.FJ Formalism.L2.Pj.QAt
open scoped ComplexConjugate
open GlobalTheory GlobalTheory.CuspFlow
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r ρ : ℕ}

theorem GlobalTheory.CuspFlow.flow_eq_zAct : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r ρ : ℕ) (X : Data E r) (cu : CuspFD X ρ), IsZBasis X cu (zBas X cu) → ∀ η : Fin ρ → E, (∑ a, η a • cu.e a) ∈ X.Λ → ∃ L : (X.Ψ → ℝ) →ₗ[ℝ] (Fin (nZ X ρ) → ℝ), (∀ s x, X.flow (∑ a, η a • cu.e a) (fun τ => (s τ : ℂ)) x = zAct X cu (L s) x) ∧ (∀ χ : Matrix (Fin ρ) (Fin ρ) E, IsHermE χ → ∀ s, ∑ k, phZ X cu χ k * L s k = 2 * ∑ τ : X.Ψ, (τ.1 (hq χ η)).re * s τ) ∧ ∀ (la : Wt X.Ψ r), ∀ p ∈ X.periods la, ∀ k, ∃ z : ℤ, L p k = z := by sorry
