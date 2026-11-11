-- Prove2me | Theorems.Thm_HiddenCorr_ERM_proposition_4
-- name    : HiddenCorr.ERM.proposition_4
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T02:36:21.6592+00:00
-- url     : https://prove2.me/theorems/72f32f32-4a98-4362-b453-6b24beb0cb77
-- title:
--   Proposition 4 — uniform covariance estimation with $w^\star$: expectation (31) and high-probability (32) bounds
-- statement:
--   There is an absolute constant $C>0$ such that the following holds. Fix a matching-covered bipartite graph $G$ with $n$ vertices on each side and a hidden matching $M\in\mathcal M(G)$, independent of the data, and suppose the pairs $(X_i,Y_{M(i)})_{i=1}^n$ are i.i.d. from a distribution $D$ on $\mathcal X\times\mathbb R$. Let $F$ be a nonempty class of functions with $\sup_{f\in F}|f(X)|\le B_F$ and $|Y|\le B_Y$ almost surely, $B_F,B_Y>0$. With the weights $w^\star=B^\top L^\dagger u/(u^\top L^\dagger u)$ and the estimator $Z_f(w^\star)$ of Eq. (30),
--   $$\mathbb E\sup_{f\in F}\big|Z_f(w^\star)-\mathrm{Cov}(f(X),Y)\big|\le\frac{CB_Y}{\sqrt{u^\top L^\dagger u}}\Big(\mathbb E\hat{\mathfrak R}_X(F)+B_F\Big),$$
--   and for every $\delta\in(0,1/e)$, with probability at least $1-\delta$,
--   $$\sup_{f\in F}\big|Z_f(w^\star)-\mathrm{Cov}(f(X),Y)\big|\le\frac{CB_Y}{\sqrt{u^\top L^\dagger u}}\Big(\hat{\mathfrak R}_X(F)\sqrt{\log(1/\delta)}+B_F\log(1/\delta)\Big).$$
--
--   This is the uniform version of covariance estimation with hidden correspondences, the probabilistic core of the learning guarantees.
--
--   Differences from the source:
--   - encoding: [n] and the sides U, V of G; a perfect matching M ∈ M(G) as a bijection U → V → Fin n, U ∪ V as Fin n ⊕ Fin n, E : Finset (Fin n × Fin n), a perfect matching as σ : Equiv.Perm (Fin n) with (i, σ i) ∈ E for all i; reason: Lean convention; the same graphs and matchings
--   - encoding: n vertices on each side (n ≥ 1 implicit: [n] indexes the sample) → hypothesis 0 < n; reason: excludes only the empty sample, where 1/√n_eff(G) is undefined (Lean would read 1/√0 = 0)
--   - encoding: the true pairs (X_i, Y_M(i)) are i.i.d. from D; the learner sees the unlinked X_1..X_n, Y_1..Y_n and G → a sample s : Fin n → X × Y drawn from Measure.pi (fun _ => D); observed X_i = (s i).1, Y_j = (s (σ⁻¹ j)).2; the learner's statistic uses E, X, Y only; reason: the paper's data-independent model (§4.1), written out
--   - reading: footnote 1 (p. 13): all functions, learning rules and suprema over function classes are measurable → the relevant functions are Measurable and the class is pointwise measurable (countable dense subclass in the pointwise sense: published IsPointwiseMeasurableClass, or its vector version IsPointwiseMeasurableClassV); reason: standard reading of the measurability convention; it makes every supremum in the statement equal to a countable one
--   - encoding: E_ε over independent Rademacher signs, conditional on the sample; complexities possibly infinite → uniform average over all sign vectors (finite sum / 2^n); R̂_X, R̂^vec_X valued in [0, ∞] (ℝ≥0∞); reason: same quantity; ℝ≥0∞ keeps an unbounded class's +∞ value
--   - encoding: real-valued bounds and expectations of suprema → both sides in ℝ≥0∞ (ENNReal.ofReal of the nonnegative real terms, lower Lebesgue integral ∫⁻ for expectations of suprema); reason: the supremum and the complexity may be +∞; all terms are nonnegative, so nothing changes for finite values
--   - encoding: with probability at least 1 − δ, … → the measure (outer measure) of the set of samples on which the claim fails is ≤ ENNReal.ofReal δ; reason: avoids requiring the failure event to be measurable; equivalent when it is measurable
--   - encoding: log, natural logarithm; δ ∈ (0, 1/e) → Real.log; 0 < δ ∧ δ < Real.exp (-1); reason: same
--   - encoding: Cov(f(X), Y) under D; |Y| ≤ B_Y and sup_f |f(X)| ≤ B_F almost surely → ∫ f(x)y dD − (∫ f(x) dD)(∫ y dD); ∀ᵐ p ∂D, |p.2| ≤ B_Y and ∀ᵐ p ∂D, ∀ f ∈ F, |f p.1| ≤ B_F; reason: same quantities
-- source:
--   Chen, Gentile, Kaplan, Koren, Supervised Learning with Hidden Correspondences, STOC 2027 submission (manuscript sha256 d0029978…), pp. 23–24, Proposition 4, Eqs. (31)–(32) (proof pp. 60–61, App. C.2)

import Mathlib
import Definitions.Def_IncrementalER_energy
import Definitions.Def_BartlettBousquetMendelson_LocalRad_IsPointwiseMeasurableClass
import Definitions.Def_HiddenCorr_ERM_CandidateGraph
import Definitions.Def_HiddenCorr_ERM_Complexity
import Definitions.Def_HiddenCorr_ERM_PseudoLabel

open MeasureTheory
open scoped ENNReal

universe u

namespace HiddenCorr.ERM

/-- **Proposition 4** (uniform covariance estimation), pp. 23–24. There is an absolute constant
`C > 0` such that: fix a matching-covered candidate graph `G` with `n ≥ 1` vertices on each side
and a hidden perfect matching `σ`, independent of the data; let the true pairs `(Xᵢ, Y_{σ(i)})` be
i.i.d. from `D` on `X × ℝ`; let `F` be a nonempty (pointwise measurable) class of measurable
functions with `sup_{f ∈ F} |f(X)| ≤ B_F` and `|Y| ≤ B_Y` almost surely, `B_F, B_Y > 0`. With the
weights `w⋆`,
`E sup_{f ∈ F} |Z_f(w⋆) − Cov(f(X), Y)| ≤ (C B_Y / √(uᵀL†u)) (E R̂_X(F) + B_F)` (Eq. (31)), and for
every `δ ∈ (0, 1/e)`, with probability at least `1 − δ`,
`sup_{f ∈ F} |Z_f(w⋆) − Cov(f(X), Y)| ≤ (C B_Y / √(uᵀL†u)) (R̂_X(F) √(log(1/δ)) + B_F log(1/δ))`
(Eq. (32)). -/
theorem proposition_4 :
    ∃ C : ℝ, 0 < C ∧
      ∀ {𝒳 : Type u} [MeasurableSpace 𝒳] (n : ℕ), 0 < n →
        ∀ (E : Finset (Fin n × Fin n)) (σ : Equiv.Perm (Fin n)),
        MatchingCovered E → IsPerfectMatching E σ →
        ∀ (D : Measure (𝒳 × ℝ)) [IsProbabilityMeasure D] (F : Set (𝒳 → ℝ)), F.Nonempty →
        (∀ f ∈ F, Measurable f) →
        BartlettBousquetMendelson.LocalRad.IsPointwiseMeasurableClass F →
        ∀ BF BY : ℝ, 0 < BF → 0 < BY →
        (∀ᵐ p ∂D, ∀ f ∈ F, |f p.1| ≤ BF) → (∀ᵐ p ∂D, |p.2| ≤ BY) →
          let μ : Measure (Fin n → 𝒳 × ℝ) := Measure.pi fun _ : Fin n => D
          let cov : (𝒳 → ℝ) → ℝ := fun f =>
            ∫ p, f p.1 * p.2 ∂D - (∫ p, f p.1 ∂D) * ∫ p, p.2 ∂D
          let dev : (𝒳 → ℝ) → (Fin n → 𝒳 × ℝ) → ℝ := fun f s =>
            |covEst E (wStar E) (fun i => f (obsX s i)) (obsY σ s) - cov f|
          (∫⁻ s, (⨆ f ∈ F, ENNReal.ofReal (dev f s)) ∂μ ≤
              ENNReal.ofReal (C * BY / Real.sqrt (neff E)) *
                (∫⁻ s, radX (obsX s) F ∂μ + ENNReal.ofReal BF)) ∧
          (∀ δ : ℝ, 0 < δ → δ < Real.exp (-1) →
            μ {s | ∃ f ∈ F,
                ENNReal.ofReal (C * BY / Real.sqrt (neff E)) *
                    (radX (obsX s) F * ENNReal.ofReal (Real.sqrt (Real.log (1 / δ))) +
                      ENNReal.ofReal (BF * Real.log (1 / δ))) <
                  ENNReal.ofReal (dev f s)} ≤ ENNReal.ofReal δ) := by sorry

end HiddenCorr.ERM
