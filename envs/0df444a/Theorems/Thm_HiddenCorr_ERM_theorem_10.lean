-- Prove2me | Theorems.Thm_HiddenCorr_ERM_theorem_10
-- name    : HiddenCorr.ERM.theorem_10
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T02:36:27.334193+00:00
-- url     : https://prove2.me/theorems/52bb2bc4-da26-4cb2-b84d-749ad5f7e60f
-- title:
--   Theorem 10 — multiclass learning with affine losses: uniform accuracy (48), excess risk $2\varepsilon+\eta$, and the Lipschitz form
-- statement:
--   There is an absolute constant $C>0$ such that the following holds. Let $k\ge2$; fix a matching-covered graph $G$ with $n$ vertices on each side and a hidden matching $M\in\mathcal M(G)$, independent of the data; the true pairs are i.i.d. from $D$ on $\mathcal X\times\{e_1,\dots,e_k\}$; $H$ is a nonempty class of $h:\mathcal X\to\mathcal Z\subset\mathbb R^k$; the loss is $\ell(z,y)=f_1(z)+\langle f_2(z),y\rangle$ with $|f_1|\le B_1$ and $\|f_2\|_2\le B_2$ on $\mathcal Z$ ($B_1,B_2>0$). Let $\hat L_G$ be the vector pseudo-label risk (Eq. (46)).
--
--   1. For every $\delta\in(0,1/e)$, with probability at least $1-\delta$,
--   $$\sup_{h\in H}|\hat L_G(h)-L(h)|\le\varepsilon:=\frac{C}{\sqrt{u^\top L^\dagger u}}\Big[\big(\hat{\mathfrak R}^{\mathrm{vec}}_X(f_1\circ H)+\hat{\mathfrak R}^{\mathrm{vec}}_X(f_2\circ H)\big)\sqrt{\log\tfrac1\delta}+(B_1+B_2)\log\tfrac1\delta\Big],$$
--   and on the same event every $\hat h$ satisfying Eq. (47) ($\hat L_G(\hat h)\le\inf_H\hat L_G+\eta$) obeys $L(\hat h)-\inf_{h\in H}L(h)\le2\varepsilon+\eta$.
--
--   2. If moreover $f_1$, $f_2$ are $L_1$-, $L_2$-Lipschitz on $\mathcal Z$, then for every $\delta\in(0,1/e)$, with probability at least $1-\delta$, every output $\hat h$ satisfying Eq. (47) obeys
--   $$L(\hat h)-\inf_{h\in H}L(h)\le\frac{C}{\sqrt{u^\top L^\dagger u}}\Big[(L_1+L_2)\hat{\mathfrak R}^{\mathrm{multi}}_X(H)\sqrt{\log\tfrac1\delta}+(B_1+B_2)\log\tfrac1\delta\Big]+\eta,$$
--   and $\sup_{h\in H}|\hat L_G(h)-L(h)|$ is at most the same right-hand side without $+\eta$.
--
--   Differences from the source:
--   - encoding: [n] and the sides U, V of G; a perfect matching M ∈ M(G) as a bijection U → V → Fin n, U ∪ V as Fin n ⊕ Fin n, E : Finset (Fin n × Fin n), a perfect matching as σ : Equiv.Perm (Fin n) with (i, σ i) ∈ E for all i; reason: Lean convention; the same graphs and matchings
--   - encoding: n vertices on each side (n ≥ 1 implicit: [n] indexes the sample) → hypothesis 0 < n; reason: excludes only the empty sample, where 1/√n_eff(G) is undefined (Lean would read 1/√0 = 0)
--   - encoding: the true pairs (X_i, Y_M(i)) are i.i.d. from D; the learner sees the unlinked X_1..X_n, Y_1..Y_n and G → a sample s : Fin n → X × Y drawn from Measure.pi (fun _ => D); observed X_i = (s i).1, Y_j = (s (σ⁻¹ j)).2; the learner's statistic uses E, X, Y only; reason: the paper's data-independent model (§4.1), written out
--   - encoding: Y = [k] ≅ {e_1, …, e_k}, hypotheses with values in {e_1, …, e_k} → labels and hypotheses Fin k-valued; one-hot vectors onehot r = e_r in the losses and pseudo-labels; reason: same objects
--   - reading: footnote 1 (p. 13): all functions, learning rules and suprema over function classes are measurable → the relevant functions are Measurable and the class is pointwise measurable (countable dense subclass in the pointwise sense: published IsPointwiseMeasurableClass, or its vector version IsPointwiseMeasurableClassV); reason: standard reading of the measurability convention; it makes every supremum in the statement equal to a countable one
--   - encoding: E_ε over independent Rademacher signs, conditional on the sample; complexities possibly infinite → uniform average over all sign vectors (finite sum / 2^n); R̂_X, R̂^vec_X valued in [0, ∞] (ℝ≥0∞); reason: same quantity; ℝ≥0∞ keeps an unbounded class's +∞ value
--   - encoding: real-valued bounds and expectations of suprema → both sides in ℝ≥0∞ (ENNReal.ofReal of the nonnegative real terms, lower Lebesgue integral ∫⁻ for expectations of suprema); reason: the supremum and the complexity may be +∞; all terms are nonnegative, so nothing changes for finite values
--   - encoding: with probability at least 1 − δ, … → the measure (outer measure) of the set of samples on which the claim fails is ≤ ENNReal.ofReal δ; reason: avoids requiring the failure event to be measurable; equivalent when it is measurable
--   - reading: on the same event, any output ĥ satisfying the η-ERM rule obeys the excess-risk bound → one failure set: the uniform-deviation bound fails for some h, or some η-minimizer ĥ violates the excess-risk bound; its measure is ≤ δ (η ≥ 0 fixed first); reason: this is what 'on the same event' asserts
--   - encoding: log, natural logarithm; δ ∈ (0, 1/e) → Real.log; 0 < δ ∧ δ < Real.exp (-1); reason: same
--   - encoding: R̂^vec_X(f₁ ∘ H) for the real-valued class f₁ ∘ H → radX (obsX s) (f₁ ∘ H); reason: Definition 3 with k = 1 coincides with Definition 2 (p. 21)
--   - encoding: f₁ : 𝒵 → ℝ, f₂ : 𝒵 → ℝ^k bounded (and Lipschitz in part 2) on 𝒵 ⊂ ℝ^k; hypotheses valued in 𝒵 → f₁, f₂ defined on ℝ^k = EuclideanSpace ℝ (Fin k) with the bounds and LipschitzOnWith (L₁ L₂ : ℝ≥0) on Z, and ∀ h ∈ H, ∀ x, h x ∈ Z; reason: values off 𝒵 are never used
--   - encoding: part 2 bound with R̂^multi_X(H) (real) → part 2 stated in EReal; reason: R̂^multi_X(H) may be +∞
--   - generalization: 'Furthermore, sup_h |L̂_G(h) − L(h)| is upper bounded by the right-hand side … without +η' → the uniform-deviation bound is part of the same failure set as the excess-risk bound of part 2; reason: one event carrying both bounds implies each of the two printed probability statements, so it specializes to the source (the proof derives both on the same event)
-- source:
--   Chen, Gentile, Kaplan, Koren, Supervised Learning with Hidden Correspondences, STOC 2027 submission (manuscript sha256 d0029978…), pp. 30–31, Theorem 10, Eq. (48) (proof pp. 62–64, App. C.4)

import Mathlib
import Definitions.Def_IncrementalER_energy
import Definitions.Def_HiddenCorr_ERM_CandidateGraph
import Definitions.Def_HiddenCorr_ERM_Complexity
import Definitions.Def_HiddenCorr_ERM_PseudoLabel

open MeasureTheory
open scoped ENNReal

universe u

namespace HiddenCorr.ERM

/-- **Theorem 10** (multiclass learning with affine losses), pp. 30–31. There is an absolute
constant `C > 0` such that: let `k ≥ 2`; fix a matching-covered candidate graph `G` with `n ≥ 1`
vertices on each side and a hidden perfect matching `σ`, independent of the data; the true pairs are
i.i.d. from `D` on `X × {e₁, …, e_k}` (labels `[k]`, one-hot); `H` is a nonempty class of
`h : X → Z ⊆ ℝ^k`; the loss is `ℓ(z, y) = f₁(z) + ⟨f₂(z), y⟩` with `|f₁| ≤ B₁`, `‖f₂‖₂ ≤ B₂` on `Z`
(`B₁, B₂ > 0`); the `f_j ∘ h` are measurable and `{(f₁ ∘ h, f₂ ∘ h)}` is pointwise measurable. Then:
1. for every `δ ∈ (0, 1/e)` and `η ≥ 0`, with probability at least `1 − δ`,
`sup_{h ∈ H} |L̂_G(h) − L(h)| ≤ ε := (C/√(uᵀL†u)) [(R̂^vec_X(f₁∘H) + R̂^vec_X(f₂∘H)) √(log(1/δ)) +
(B₁ + B₂) log(1/δ)]` (Eq. (48)), and on the same event every `ĥ` satisfying Eq. (47) has
`L(ĥ) − inf_H L ≤ 2ε + η`;
2. if moreover `f₁`, `f₂` are `L₁`-, `L₂`-Lipschitz on `Z`, then for every `δ ∈ (0, 1/e)` and
`η ≥ 0`, with probability at least `1 − δ`, every `ĥ` satisfying Eq. (47) has
`L(ĥ) − inf_H L ≤ (C/√(uᵀL†u)) [(L₁ + L₂) R̂^multi_X(H) √(log(1/δ)) + (B₁ + B₂) log(1/δ)] + η`,
and `sup_{h ∈ H} |L̂_G(h) − L(h)|` is at most the same right-hand side without `+ η`. -/
theorem theorem_10 :
    ∃ C : ℝ, 0 < C ∧
      ∀ {𝒳 : Type u} [MeasurableSpace 𝒳] (k : ℕ), 2 ≤ k → ∀ (n : ℕ), 0 < n →
        ∀ (E : Finset (Fin n × Fin n)) (σ : Equiv.Perm (Fin n)),
        MatchingCovered E → IsPerfectMatching E σ →
        ∀ (D : Measure (𝒳 × Fin k)) [IsProbabilityMeasure D]
          (Z : Set (EuclideanSpace ℝ (Fin k))) (H : Set (𝒳 → EuclideanSpace ℝ (Fin k))),
        H.Nonempty → (∀ h ∈ H, ∀ x, h x ∈ Z) →
        ∀ (f₁ : EuclideanSpace ℝ (Fin k) → ℝ)
          (f₂ : EuclideanSpace ℝ (Fin k) → EuclideanSpace ℝ (Fin k)) (B₁ B₂ : ℝ),
        0 < B₁ → 0 < B₂ → (∀ z ∈ Z, |f₁ z| ≤ B₁) → (∀ z ∈ Z, ‖f₂ z‖ ≤ B₂) →
        (∀ h ∈ H, Measurable (fun x => f₁ (h x)) ∧ Measurable (fun x => f₂ (h x))) →
        IsPointwiseMeasurableClassV ((fun h x => (f₁ (h x), f₂ (h x))) '' H) →
          let μ : Measure (Fin n → 𝒳 × Fin k) := Measure.pi fun _ : Fin n => D
          let Lhat : (𝒳 → EuclideanSpace ℝ (Fin k)) → (Fin n → 𝒳 × Fin k) → ℝ := fun h s =>
            pseudoRiskVec E f₁ f₂ h (obsX s) (obsY σ s)
          let L : (𝒳 → EuclideanSpace ℝ (Fin k)) → ℝ := fun h => riskAffineVec D f₁ f₂ h
          let r : ℝ := C / Real.sqrt (neff E)
          (∀ δ η : ℝ, 0 < δ → δ < Real.exp (-1) → 0 ≤ η →
            let ε : (Fin n → 𝒳 × Fin k) → ℝ≥0∞ := fun s =>
              ENNReal.ofReal r *
                ((radX (obsX s) ((fun h => f₁ ∘ h) '' H) +
                      radVec (obsX s) ((fun h => f₂ ∘ h) '' H)) *
                    ENNReal.ofReal (Real.sqrt (Real.log (1 / δ))) +
                  ENNReal.ofReal ((B₁ + B₂) * Real.log (1 / δ)))
            μ {s | (∃ h ∈ H, ε s < ENNReal.ofReal |Lhat h s - L h|) ∨
                (∃ ĥ ∈ H, Lhat ĥ s ≤ sInf ((fun h => Lhat h s) '' H) + η ∧
                  2 * ε s + ENNReal.ofReal η < ENNReal.ofReal (L ĥ - sInf (L '' H)))} ≤
              ENNReal.ofReal δ) ∧
          (∀ L₁ L₂ : NNReal, LipschitzOnWith L₁ f₁ Z → LipschitzOnWith L₂ f₂ Z →
            ∀ δ η : ℝ, 0 < δ → δ < Real.exp (-1) → 0 ≤ η →
              let b : (Fin n → 𝒳 × Fin k) → EReal := fun s =>
                (r : EReal) *
                  ((((L₁ : ℝ) + (L₂ : ℝ) : ℝ) : EReal) * radMulti (obsX s) H *
                      (Real.sqrt (Real.log (1 / δ)) : EReal) +
                    (((B₁ + B₂) * Real.log (1 / δ) : ℝ) : EReal))
              μ {s | (∃ ĥ ∈ H, Lhat ĥ s ≤ sInf ((fun h => Lhat h s) '' H) + η ∧
                    b s + (η : EReal) < ((L ĥ - sInf (L '' H) : ℝ) : EReal)) ∨
                  (∃ h ∈ H, b s < ((|Lhat h s - L h| : ℝ) : EReal))} ≤
                ENNReal.ofReal δ) := by sorry

end HiddenCorr.ERM
