-- Prove2me | Theorems.Thm_GlobalTheory_QuadraticZeta_hasSum_ideal
-- name    : GlobalTheory.QuadraticZeta.hasSum_ideal
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T19:12:18.391222+00:00
-- url     : https://prove2.me/theorems/da89fab4-84a2-48e0-b764-85cb285ee7a3
-- title:
--   Quadratic Zeta: has Sum ideal
-- statement:
--   The Quadratic Zeta construction uses the has Sum ideal property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/ExistsBasisEmbedding.lean#L111-L167
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/ExistsBasisEmbedding.lean#L111-L167

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsIsKroneckerCharOfDiscr
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsVariableChangeEqLatticeCurve
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsBasisEmbedding
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Module FractionalIdeal
open scoped nonZeroDivisors UpperHalfPlane ComplexConjugate
open GlobalTheory GlobalTheory.QuadraticZeta
variable {K : Type*} [Field K] [NumberField K] {d : ℕ}
variable (h2 : finrank ℚ K = 2) (hD : discr K = -d) (σ : K →+* ℂ)
include h2 hD

theorem GlobalTheory.QuadraticZeta.hasSum_ideal (hd : 4 < d) (𝔞 : (FractionalIdeal (𝓞 K)⁰ K)ˣ) {s S : ℝ} (hs : s ≠ 0)
    (h : HasSum (fun x : ((𝔞 : FractionalIdeal (𝓞 K)⁰ K) : Submodule (𝓞 K) K) =>
      (‖σ x‖ ^ 2 / absNorm 𝔞.1) ^ (-s)) S) :
    HasSum (fun I : Ideal (𝓞 K) => open Classical in
      if ((I * 𝔞 : FractionalIdeal (𝓞 K)⁰ K) : Submodule (𝓞 K) K).IsPrincipal
      then 2 * (Ideal.absNorm I : ℝ) ^ (-s) else 0) S := by sorry
