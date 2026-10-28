-- Prove2me | Theorems.Thm_OAI_HyperbolicCoding_block_recoding_small_cost_q44
-- name    : OAI.HyperbolicCoding.block_recoding_small_cost_q44
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-27T12:04:15.286993+00:00
-- url     : https://prove2.me/theorems/6d16d8bf-34fd-4ab5-9356-5ad9e714acd1
-- title:
--   OAI.HyperbolicCoding.block_recoding_small_cost_q44: intermediate lemma from OpenAI, Positive Metric Entropy for the Standard Map at Large Parameters
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.StandardMapEntropy.main_components`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Positive Metric Entropy for the Standard Map at Large Parameters*, OpenAI Math Release, September 23, 2026, result family 146, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.HyperbolicCoding.block_recoding_small_cost` of [lean/OAI/Dynamics/StandardMap/StandardMap/Coupling/ActualFiniteRecodingBounds.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Dynamics/StandardMap/StandardMap/Coupling/ActualFiniteRecodingBounds.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.HyperbolicCoding`, with `open MeasureTheory Set StandardMapEntropy.Entropy`, `open scoped BigOperators ENNReal`):
--
--   ```lean
--   lemma block_recoding_small_cost_q44 [StandardBorelSpace X] [StandardBorelSpace Y]
--       (μ : Measure X) (ν : Measure Y)
--       [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] [NullSingletonClass μ]
--       (e : X ≃ᵐ X) (he : MeasurePreserving e μ μ) (r : X → A) (hr : Measurable r)
--       (k g L n J : ℕ) (V : Y → Fin n → Fin J → Fin (k+g) → A) (hV : Measurable V)
--       {a δ : ℝ} (ha : 0<a) (hδ₀ : 0≤δ) (hδ : δ≤a)
--       (hgap : (g : ℝ)≤a*k) (hB₁ : 2+(L : ℝ)*Real.log (Fintype.card (Fin (k+g) → A))≤(J : ℝ)*a^2)
--       (hB₂ : 2*(L : ℝ)≤(J : ℝ)*a)
--       (hremote : ∀ T : ℕ,LawClose
--         (μ.map (fun x => (word e r T (e^[k+g] x),word e r k x)))
--         ((μ.map (fun x => word e r T (e^[k+g] x))).prod (μ.map (word e r k))) a)
--       (hlaw : ∀ I : Fin n,LawClose
--         (μ.map (word (e^[k+g]) (word e r (k+g)) J)) (ν.map (fun y => V y I)) δ)
--       (htest : ∀ (q : Y → Fin (k+g) → A) (v : Y → Fin L → Fin (k+g) → A),
--         Measurable q → Measurable v →
--         LawClose (μ.map (fun x => (word e r (k+g) x,
--           word (e^[k+g]) (word e r (k+g)) L (e^[k+g] x))))
--           (ν.map (fun y => (q y,v y))) δ → StandardMapEntropy.Entropy.cond ν q v≤
--             (k+g : ℕ)*rate μ e r+a^2)
--       (hentropy : ((n*J)*(k+g) : ℕ)*rate μ e r-2*(n*J : ℕ)*a^2-2*(n : ℝ)≤
--         obs ν (nestedOutput n J (k+g) V)) :
--       ∃ R : MatrixCoupling (mass μ (word e r ((n*J)*(k+g))))
--           (mass ν (nestedOutput n J (k+g) V)),
--         R.cost nameCost≤17*a*((n*J)*(k+g) : ℕ)
--   ```
--
--   **Definitions.** The statement is written with `OAI.HyperbolicCoding.LawClose`, `OAI.HyperbolicCoding.MatrixCoupling`, `OAI.HyperbolicCoding.nameCost`, `OAI.HyperbolicCoding.nestedOutput`, `OAI.HyperbolicCoding.MatrixCoupling.cost`, `OAI.StandardMapEntropy.Entropy.cond`, `OAI.StandardMapEntropy.Entropy.mass`, `OAI.StandardMapEntropy.Entropy.obs`, `OAI.StandardMapEntropy.Entropy.rate` and `OAI.StandardMapEntropy.Entropy.word` (definitions bundle `OAIQ44C000` of this split).
--
--   **Used by.** The proof of `OAI.HyperbolicCoding.fixed_decoder_arbitrary_tests_q44` of this split imports it.
-- source:
--   OpenAI, Positive Metric Entropy for the Standard Map at Large Parameters, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 146; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Positive-Metric-Entropy-for-the-Standard-Map-at-Large-Parameters-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Dynamics/StandardMap/StandardMap/Coupling/ActualFiniteRecodingBounds.lean (declaration OAI.HyperbolicCoding.block_recoding_small_cost)

import Mathlib
import Definitions.Def_OAIQ44C000

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace HyperbolicCoding
open MeasureTheory Set StandardMapEntropy.Entropy
open scoped BigOperators ENNReal
variable {X Y A : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    [MeasurableSpace A] [Fintype A] [MeasurableSingletonClass A] [Nonempty A]

lemma block_recoding_small_cost_q44 [StandardBorelSpace X] [StandardBorelSpace Y]
    (μ : Measure X) (ν : Measure Y)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] [NullSingletonClass μ]
    (e : X ≃ᵐ X) (he : MeasurePreserving e μ μ) (r : X → A) (hr : Measurable r)
    (k g L n J : ℕ) (V : Y → Fin n → Fin J → Fin (k+g) → A) (hV : Measurable V)
    {a δ : ℝ} (ha : 0<a) (hδ₀ : 0≤δ) (hδ : δ≤a)
    (hgap : (g : ℝ)≤a*k) (hB₁ : 2+(L : ℝ)*Real.log (Fintype.card (Fin (k+g) → A))≤(J : ℝ)*a^2)
    (hB₂ : 2*(L : ℝ)≤(J : ℝ)*a)
    (hremote : ∀ T : ℕ,LawClose
      (μ.map (fun x => (word e r T (e^[k+g] x),word e r k x)))
      ((μ.map (fun x => word e r T (e^[k+g] x))).prod (μ.map (word e r k))) a)
    (hlaw : ∀ I : Fin n,LawClose
      (μ.map (word (e^[k+g]) (word e r (k+g)) J)) (ν.map (fun y => V y I)) δ)
    (htest : ∀ (q : Y → Fin (k+g) → A) (v : Y → Fin L → Fin (k+g) → A),
      Measurable q → Measurable v →
      LawClose (μ.map (fun x => (word e r (k+g) x,
        word (e^[k+g]) (word e r (k+g)) L (e^[k+g] x))))
        (ν.map (fun y => (q y,v y))) δ → StandardMapEntropy.Entropy.cond ν q v≤
          (k+g : ℕ)*rate μ e r+a^2)
    (hentropy : ((n*J)*(k+g) : ℕ)*rate μ e r-2*(n*J : ℕ)*a^2-2*(n : ℝ)≤
      obs ν (nestedOutput n J (k+g) V)) :
    ∃ R : MatrixCoupling (mass μ (word e r ((n*J)*(k+g))))
        (mass ν (nestedOutput n J (k+g) V)),
      R.cost nameCost≤17*a*((n*J)*(k+g) : ℕ) := by
  sorry
end HyperbolicCoding

end

end OAI
end
