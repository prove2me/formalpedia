-- Prove2me | Theorems.Thm_GlobalTheory_chowla_selberg_discriminant
-- name    : GlobalTheory.chowla_selberg_discriminant
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T22:03:31.507305+00:00
-- url     : https://prove2.me/theorems/5e7f7add-cba6-457b-983b-05ca354cf67f
-- title:
--   Global Theory: chowla selberg discriminant
-- statement:
--   The Global Theory construction uses the chowla selberg discriminant property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/DedekindZetaEqSumRealEisenstein.lean#L259-L287
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/DedekindZetaEqSumRealEisenstein.lean#L259-L287

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_TendstoRealEisensteinSubPole
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsBasisEmbedding
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_DedekindZetaEqSumRealEisenstein
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Module FractionalIdeal Filter Topology
open scoped nonZeroDivisors UpperHalfPlane Real
open GlobalTheory
open QuadraticZeta
variable {K : Type*} [Field K] [NumberField K] {d : ℕ}
variable [NeZero d] (h2 : finrank ℚ K = 2) (hD : discr K = -d) (hd : 4 < d)
  {χ : DirichletCharacter ℂ d} (hχ : IsKroneckerChar χ) (σ : K →+* ℂ)
include h2 hD hd hχ
variable {𝔞 : ClassGroup (𝓞 K) → (FractionalIdeal (𝓞 K)⁰ K)ˣ}
  (h𝔞 : ∀ c, ClassGroup.mk K (𝔞 c) = c) {L : ClassGroup (𝓞 K) → PeriodPair}
  (hL : ∀ c, ((L c).lattice : Set ℂ) = σ '' (𝔞 c).1)
include h𝔞 hL

theorem GlobalTheory.chowla_selberg_discriminant :
    (((∑ c, Real.log ((absNorm (𝔞 c).1 : ℝ) ^ 6 * ‖(L c).g₂ ^ 3 - 27 * (L c).g₃ ^ 2‖))
        / classNumber K : ℝ) : ℂ)
      = (12 * Real.log (2 * π) - 6 * Real.log d + 6 * Real.eulerMascheroniConstant : ℝ)
        - 6 * (deriv χ.LFunction 1 / χ.LFunction 1) := by sorry
