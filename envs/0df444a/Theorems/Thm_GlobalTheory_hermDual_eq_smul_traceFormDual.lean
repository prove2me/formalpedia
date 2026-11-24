-- Prove2me | Theorems.Thm_GlobalTheory_hermDual_eq_smul_traceFormDual
-- name    : GlobalTheory.hermDual_eq_smul_traceFormDual
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T22:55:14.802853+00:00
-- url     : https://prove2.me/theorems/5062b3fe-7673-4a35-85ef-77b4257d572c
-- title:
--   Global Theory: herm Dual eq smul trace Form Dual
-- statement:
--   The Global Theory construction uses the herm Dual eq smul trace Form Dual property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HermitianTraceForms/TraceFormDualOneTraceFormDual.lean#L316-L322
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HermitianTraceForms/TraceFormDualOneTraceFormDual.lean#L316-L322

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_HermitianTraceFormVanishing
import Definitions.Def_ReciprocityTheory_SemistableReduction_TorsionNonvanishStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HermitianTraceForms_TraceFormDualOneTraceFormDual
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing
open scoped nonZeroDivisors
noncomputable section
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}
variable {G : Matrix (Fin r) (Fin r) E} {Λ Λ₁ Λ₂ : Submodule (𝓞 E) (Fin r → E)}

theorem GlobalTheory.hermDual_eq_smul_traceFormDual {ξ : E} (hξ : ξ ≠ 0) :
    hermDual G Λ =
      ((FractionalIdeal.spanSingleton (𝓞 E)⁰ ξ *
        (differentIdeal ℤ (𝓞 E) : Ideal (𝓞 E)) : FractionalIdeal (𝓞 E)⁰ E) :
          Submodule (𝓞 E) E) • traceFormDual ξ G Λ := by sorry
