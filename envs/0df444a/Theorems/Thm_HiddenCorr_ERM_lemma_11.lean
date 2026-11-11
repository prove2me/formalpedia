-- Prove2me | Theorems.Thm_HiddenCorr_ERM_lemma_11
-- name    : HiddenCorr.ERM.lemma_11
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T02:35:20.25607+00:00
-- url     : https://prove2.me/theorems/3dd7c863-cf90-4147-ab3f-d7afb467c68e
-- title:
--   Lemma 11 — empirical-process comparison: $\mathbb EZ\le2\mathbb ER$, tail and $L_p$ bounds for $(Z-2R)_+$
-- statement:
--   There is an absolute constant $C>0$ such that the following holds. Let $U_1,\dots,U_m$ be independent random variables and let $\mathcal G$ be a nonempty class of real-valued functions with $\sup_{g\in\mathcal G}|g(U_i)|\le B$ almost surely for every $i$, where $B>0$. For deterministic weights $a_1,\dots,a_m$ define
--   $$Z=\sup_{g\in\mathcal G}\Big|\sum_i a_i\big(g(U_i)-\mathbb Eg(U_i)\big)\Big|,\qquad R=\mathbb E_\varepsilon\sup_{g\in\mathcal G}\Big|\sum_i\varepsilon_i a_i g(U_i)\Big|,$$
--   with independent Rademacher signs $\varepsilon_i$, independent of the sample. Then $\mathbb EZ\le2\,\mathbb ER$; for every $t\ge0$, with probability at least $1-2e^{-t}$,
--   $$Z\le 2R+CB\Big(\sum_i a_i^2\Big)^{1/2}\sqrt t;$$
--   and for every $p\ge1$, $\|(Z-2R)_+\|_{L_p}\le CB(\sum_i a_i^2)^{1/2}\sqrt p$.
--
--   This is symmetrization combined with bounded differences; the paper uses it for the diagonal terms and the conditional off-diagonal terms of Theorem 7 and for the marginal means in Theorems 8 and 10.
--
--   Differences from the source:
--   - reading: footnote 1 (p. 13): all functions, learning rules and suprema over function classes are measurable → the relevant functions are Measurable and the class is pointwise measurable (countable dense subclass in the pointwise sense: published IsPointwiseMeasurableClass, or its vector version IsPointwiseMeasurableClassV); reason: standard reading of the measurability convention; it makes every supremum in the statement equal to a countable one
--   - encoding: Z, R real, (Z − 2R)₊, ‖W‖_{L_p} = (E|W|^p)^{1/p} → Z, R valued in ℝ≥0∞; (Z − 2R)₊ as truncated subtraction Z − 2R in ℝ≥0∞; ‖W‖_{L_p} as (∫⁻ W^p)^{1/p}; E as ∫⁻; reason: R is finite almost surely (|g(Uᵢ)| ≤ B), where truncated subtraction is the positive part
--   - encoding: with probability at least 1 − δ, … → the measure (outer measure) of the set of samples on which the claim fails is ≤ ENNReal.ofReal δ; reason: avoids requiring the failure event to be measurable; equivalent when it is measurable
--   - encoding: E_ε over independent signs → uniform average over the 2^m sign vectors (rademacherAvg); reason: same quantity
-- source:
--   Chen, Gentile, Kaplan, Koren, Supervised Learning with Hidden Correspondences, STOC 2027 submission (manuscript sha256 d0029978…), p. 61, Lemma 11 (App. C.3)

import Mathlib
import Definitions.Def_BartlettBousquetMendelson_LocalRad_IsPointwiseMeasurableClass
import Definitions.Def_HiddenCorr_ERM_Complexity

open MeasureTheory ProbabilityTheory
open scoped ENNReal

universe u v

namespace HiddenCorr.ERM

/-- **Lemma 11** (empirical-process comparison), p. 61. There is an absolute constant `C > 0` such
that: let `U₁, …, U_m` be independent random variables and `G` a nonempty (pointwise
measurable) class of measurable real functions with `sup_{g ∈ G} |g(Uᵢ)| ≤ B` almost surely for every `i`,
`B > 0`. For deterministic weights `a₁, …, a_m` put
`Z = sup_{g ∈ G} |∑ᵢ aᵢ (g(Uᵢ) − E g(Uᵢ))|` and `R = E_ε sup_{g ∈ G} |∑ᵢ εᵢ aᵢ g(Uᵢ)|`.
Then `E Z ≤ 2 E R`; for every `t ≥ 0`, with probability at least `1 − 2e^{−t}`,
`Z ≤ 2R + C B (∑ᵢ aᵢ²)^{1/2} √t`; and for every `p ≥ 1`,
`‖(Z − 2R)₊‖_{L_p} ≤ C B (∑ᵢ aᵢ²)^{1/2} √p`. -/
theorem lemma_11 :
    ∃ C : ℝ, 0 < C ∧
      ∀ {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        {𝒰 : Type v} [MeasurableSpace 𝒰] (m : ℕ) (U : Fin m → Ω → 𝒰),
        (∀ i, Measurable (U i)) → iIndepFun U P →
        ∀ G : Set (𝒰 → ℝ), G.Nonempty → (∀ g ∈ G, Measurable g) →
        BartlettBousquetMendelson.LocalRad.IsPointwiseMeasurableClass G →
        ∀ B : ℝ, 0 < B → (∀ i, ∀ᵐ ω ∂P, ∀ g ∈ G, |g (U i ω)| ≤ B) →
        ∀ a : Fin m → ℝ,
          let Z : Ω → ℝ≥0∞ := fun ω =>
            ⨆ g ∈ G, ENNReal.ofReal |∑ i, a i * (g (U i ω) - ∫ ω', g (U i ω') ∂P)|
          let R : Ω → ℝ≥0∞ := fun ω => rademacherAvg a (fun i => U i ω) G
          (∫⁻ ω, Z ω ∂P ≤ 2 * ∫⁻ ω, R ω ∂P) ∧
          (∀ t : ℝ, 0 ≤ t →
            P {ω | 2 * R ω + ENNReal.ofReal (C * B * Real.sqrt (∑ i, a i ^ 2) * Real.sqrt t) <
                Z ω} ≤ ENNReal.ofReal (2 * Real.exp (-t))) ∧
          (∀ p : ℝ, 1 ≤ p →
            (∫⁻ ω, (Z ω - 2 * R ω) ^ p ∂P) ^ (1 / p) ≤
              ENNReal.ofReal (C * B * Real.sqrt (∑ i, a i ^ 2) * Real.sqrt p)) := by sorry

end HiddenCorr.ERM
