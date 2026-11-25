-- Prove2me | Theorems.Thm_GlobalTheory_TraceIsometry_exists_gl_of_trace_isometry
-- name    : GlobalTheory.TraceIsometry.exists_gl_of_trace_isometry
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T12:43:42.289851+00:00
-- url     : https://prove2.me/theorems/00e53aec-ffba-4165-b863-df66427ed313
-- title:
--   Trace Isometry: exists gl of trace isometry
-- statement:
--   The Trace Isometry construction uses the exists gl of trace isometry property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/ExistsRationalIsometryOfTraceIsometry.lean#L46-L132
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/ExistsRationalIsometryOfTraceIsometry.lean#L46-L132

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_Signature
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsLevelBlockOfEq
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_ExistsRationalIsometryOfTraceIsometry
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD
open scoped Matrix
open GlobalTheory GlobalTheory.TraceIsometry
variable {E : Type} [Field E] [NumberField E] [IsCMField E]
open NumberField
open scoped Matrix
variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem GlobalTheory.TraceIsometry.exists_gl_of_trace_isometry : ∀ (E : Type) [Field E] [NumberField E]
    [IsCMField E] (r : ℕ) (X X' : _root_.ReciprocityTheory.ChartRestriction.G.FD.Data E r), (∀ τ : E →+* ℂ, ‖τ X.ξ0‖ = ‖τ X'.ξ0‖) →
    ∀ (gam : X.Λ ≃ₗ[𝓞 E] X'.Λ), (∀ u v : X.Λ, Algebra.trace ℚ E (-X'.ξ0 * _root_.ReciprocityTheory.ChartRestriction.G.FD.herm X'.Gm
    (gam u : Fin r → E) (gam v : Fin r → E)) = Algebra.trace ℚ E (-X.ξ0 * _root_.ReciprocityTheory.ChartRestriction.G.FD.herm X.Gm
    (u : Fin r → E) (v : Fin r → E))) → ∃ (a : GL (Fin r) E) (ε : E), (ε = 1 ∨ ε = -1) ∧
    X'.ξ0 = ε * X.ξ0 ∧ (∀ v : X.Λ, (a : Matrix (Fin r) (Fin r) E) *ᵥ (v : Fin r → E) =
    (gam v : Fin r → E)) ∧ (∀ v, v ∈ X.Λ ↔ (a : Matrix (Fin r) (Fin r) E) *ᵥ v ∈ X'.Λ) ∧
    ∀ u v, _root_.ReciprocityTheory.ChartRestriction.G.FD.herm X'.Gm ((a : Matrix (Fin r) (Fin r) E) *ᵥ u)
    ((a : Matrix (Fin r) (Fin r) E) *ᵥ v) = ε * _root_.ReciprocityTheory.ChartRestriction.G.FD.herm X.Gm u v := by sorry
