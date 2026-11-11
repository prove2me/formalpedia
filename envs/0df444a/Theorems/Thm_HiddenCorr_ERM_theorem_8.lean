-- Prove2me | Theorems.Thm_HiddenCorr_ERM_theorem_8
-- name    : HiddenCorr.ERM.theorem_8
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T02:36:25.226199+00:00
-- url     : https://prove2.me/theorems/d1852e6a-3d82-4c7a-b45f-eb474af88a56
-- title:
--   Theorem 8 — learning with affine losses: uniform accuracy (39) of $\hat L_G$, excess risk $2\varepsilon+\eta$, and the Lipschitz form
-- statement:
--   There is an absolute constant $C>0$ such that the following holds. Fix a matching-covered graph $G$ with $n$ vertices on each side and a hidden matching $M\in\mathcal M(G)$, independent of the data; the true pairs are i.i.d. from $D$ on $\mathcal X\times\mathcal Y$ with $\mathcal Y\subseteq[-B_Y,B_Y]$; $H$ is a nonempty class of $h:\mathcal X\to\mathcal Z\subseteq\mathbb R$; the loss is $\ell(z,y)=f_1(z)+yf_2(z)$ with $|f_1|\le B_1$, $|f_2|\le B_2$ on $\mathcal Z$ ($B_Y,B_1,B_2>0$). Let $\hat L_G$ be the pseudo-label risk (Eq. (35)) and $L(h)=\mathbb E\,\ell(h(X),Y)$.
--
--   1. For every $\delta\in(0,1/e)$, with probability at least $1-\delta$,
--   $$\sup_{h\in H}|\hat L_G(h)-L(h)|\le\varepsilon:=\frac{C}{\sqrt{u^\top L^\dagger u}}\Big[\big(\hat{\mathfrak R}_X(f_1\circ H)+B_Y\hat{\mathfrak R}_X(f_2\circ H)\big)\sqrt{\log\tfrac1\delta}+(B_1+B_YB_2)\log\tfrac1\delta\Big],$$
--   and on the same event every $\hat h\in H$ with $\hat L_G(\hat h)\le\inf_{h\in H}\hat L_G(h)+\eta$ (Eq. (36), $\eta\ge0$) obeys $L(\hat h)-\inf_{h\in H}L(h)\le2\varepsilon+\eta$.
--
--   2. If moreover $f_1$ and $f_2$ are $L_1$- and $L_2$-Lipschitz on $\mathcal Z$, then for every $\delta\in(0,1/e)$, with probability at least $1-\delta$, every such $\hat h$ obeys
--   $$L(\hat h)-\inf_{h\in H}L(h)\le\frac{C}{\sqrt{u^\top L^\dagger u}}\Big[(L_1+B_YL_2)\hat{\mathfrak R}_X(H)\sqrt{\log\tfrac1\delta}+(B_1+B_YB_2)\log\tfrac1\delta\Big]+\eta.$$
--
--   Both hold for every fixed hidden matching and every distribution $D$. This is the general guarantee of pseudo-label ERM for scalar affine losses.
--
--   Differences from the source:
--   - encoding: [n] and the sides U, V of G; a perfect matching M ∈ M(G) as a bijection U → V → Fin n, U ∪ V as Fin n ⊕ Fin n, E : Finset (Fin n × Fin n), a perfect matching as σ : Equiv.Perm (Fin n) with (i, σ i) ∈ E for all i; reason: Lean convention; the same graphs and matchings
--   - encoding: n vertices on each side (n ≥ 1 implicit: [n] indexes the sample) → hypothesis 0 < n; reason: excludes only the empty sample, where 1/√n_eff(G) is undefined (Lean would read 1/√0 = 0)
--   - encoding: the true pairs (X_i, Y_M(i)) are i.i.d. from D; the learner sees the unlinked X_1..X_n, Y_1..Y_n and G → a sample s : Fin n → X × Y drawn from Measure.pi (fun _ => D); observed X_i = (s i).1, Y_j = (s (σ⁻¹ j)).2; the learner's statistic uses E, X, Y only; reason: the paper's data-independent model (§4.1), written out
--   - reading: footnote 1 (p. 13): all functions, learning rules and suprema over function classes are measurable → the relevant functions are Measurable and the class is pointwise measurable (countable dense subclass in the pointwise sense: published IsPointwiseMeasurableClass, or its vector version IsPointwiseMeasurableClassV); reason: standard reading of the measurability convention; it makes every supremum in the statement equal to a countable one
--   - encoding: E_ε over independent Rademacher signs, conditional on the sample; complexities possibly infinite → uniform average over all sign vectors (finite sum / 2^n); R̂_X, R̂^vec_X valued in [0, ∞] (ℝ≥0∞); reason: same quantity; ℝ≥0∞ keeps an unbounded class's +∞ value
--   - encoding: real-valued bounds and expectations of suprema → both sides in ℝ≥0∞ (ENNReal.ofReal of the nonnegative real terms, lower Lebesgue integral ∫⁻ for expectations of suprema); reason: the supremum and the complexity may be +∞; all terms are nonnegative, so nothing changes for finite values
--   - encoding: with probability at least 1 − δ, … → the measure (outer measure) of the set of samples on which the claim fails is ≤ ENNReal.ofReal δ; reason: avoids requiring the failure event to be measurable; equivalent when it is measurable
--   - reading: on the same event, any output ĥ satisfying the η-ERM rule obeys the excess-risk bound → one failure set: the uniform-deviation bound fails for some h, or some η-minimizer ĥ violates the excess-risk bound; its measure is ≤ δ (η ≥ 0 fixed first); reason: this is what 'on the same event' asserts
--   - encoding: log, natural logarithm; δ ∈ (0, 1/e) → Real.log; 0 < δ ∧ δ < Real.exp (-1); reason: same
--   - encoding: label space 𝒴 ⊆ [−B_Y, B_Y], D on 𝒳 × 𝒴 → D on 𝒳 × ℝ with ∀ᵐ p ∂D, |p.2| ≤ B_Y; reason: the same distributions, viewed on ℝ
--   - encoding: f₁, f₂ : 𝒵 → ℝ bounded (and Lipschitz in part 2) on 𝒵 ⊆ ℝ; hypotheses with values in 𝒵 → f₁, f₂ : ℝ → ℝ with the bounds and LipschitzOnWith on Z, and ∀ h ∈ H, ∀ x, h x ∈ Z; only fⱼ ∘ h enters; reason: any function on 𝒵 extends to ℝ; values off 𝒵 are never used
--   - encoding: Lipschitz constants L₁, L₂ ≥ 0 → L₁ L₂ : ℝ≥0; reason: Lean convention
-- source:
--   Chen, Gentile, Kaplan, Koren, Supervised Learning with Hidden Correspondences, STOC 2027 submission (manuscript sha256 d0029978…), p. 26, Theorem 8, Eq. (39) (proof pp. 27–28)

import Mathlib
import Definitions.Def_IncrementalER_energy
import Definitions.Def_HiddenCorr_ERM_CandidateGraph
import Definitions.Def_HiddenCorr_ERM_Complexity
import Definitions.Def_HiddenCorr_ERM_PseudoLabel

open MeasureTheory
open scoped ENNReal

universe u

namespace HiddenCorr.ERM

/-- **Theorem 8** (learning with affine losses), p. 26. There is an absolute constant `C > 0` such
that: fix a matching-covered candidate graph `G` with `n ≥ 1` vertices on each side and a hidden
perfect matching `σ`, independent of the data; the true pairs are i.i.d. from `D` on `X × ℝ` with
`|Y| ≤ B_Y` almost surely; `H` is a nonempty class of `h : X → Z ⊆ ℝ`; the loss is
`ℓ(z, y) = f₁(z) + y f₂(z)` with `|f₁| ≤ B₁`, `|f₂| ≤ B₂` on `Z` (`B_Y, B₁, B₂ > 0`); the functions
`f_j ∘ h` are measurable and the class `{(f₁ ∘ h, f₂ ∘ h)}` is pointwise measurable. Write
`L̂_G` for the pseudo-label risk (Eq. (35)) and `L` for the risk. Then:
1. for every `δ ∈ (0, 1/e)` and tolerance `η ≥ 0`, with probability at least `1 − δ`,
`sup_{h ∈ H} |L̂_G(h) − L(h)| ≤ ε := (C/√(uᵀL†u)) [(R̂_X(f₁∘H) + B_Y R̂_X(f₂∘H)) √(log(1/δ)) +
(B₁ + B_Y B₂) log(1/δ)]` (Eq. (39)), and on the same event every `ĥ ∈ H` with
`L̂_G(ĥ) ≤ inf_H L̂_G + η` (Eq. (36)) has `L(ĥ) − inf_H L ≤ 2ε + η`;
2. if moreover `f₁`, `f₂` are `L₁`-, `L₂`-Lipschitz on `Z`, then for every `δ ∈ (0, 1/e)` and
`η ≥ 0`, with probability at least `1 − δ`, every such `ĥ` has
`L(ĥ) − inf_H L ≤ (C/√(uᵀL†u)) [(L₁ + B_Y L₂) R̂_X(H) √(log(1/δ)) + (B₁ + B_Y B₂) log(1/δ)] + η`. -/
theorem theorem_8 :
    ∃ C : ℝ, 0 < C ∧
      ∀ {𝒳 : Type u} [MeasurableSpace 𝒳] (n : ℕ), 0 < n →
        ∀ (E : Finset (Fin n × Fin n)) (σ : Equiv.Perm (Fin n)),
        MatchingCovered E → IsPerfectMatching E σ →
        ∀ (D : Measure (𝒳 × ℝ)) [IsProbabilityMeasure D] (BY : ℝ), 0 < BY →
        (∀ᵐ p ∂D, |p.2| ≤ BY) →
        ∀ (Z : Set ℝ) (H : Set (𝒳 → ℝ)), H.Nonempty → (∀ h ∈ H, ∀ x, h x ∈ Z) →
        ∀ (f₁ f₂ : ℝ → ℝ) (B₁ B₂ : ℝ), 0 < B₁ → 0 < B₂ →
        (∀ z ∈ Z, |f₁ z| ≤ B₁) → (∀ z ∈ Z, |f₂ z| ≤ B₂) →
        (∀ h ∈ H, Measurable (fun x => f₁ (h x)) ∧ Measurable (fun x => f₂ (h x))) →
        IsPointwiseMeasurableClassV ((fun h x => (f₁ (h x), f₂ (h x))) '' H) →
          let μ : Measure (Fin n → 𝒳 × ℝ) := Measure.pi fun _ : Fin n => D
          let Lhat : (𝒳 → ℝ) → (Fin n → 𝒳 × ℝ) → ℝ := fun h s =>
            pseudoRisk E f₁ f₂ h (obsX s) (obsY σ s)
          let L : (𝒳 → ℝ) → ℝ := fun h => riskAffine D f₁ f₂ h
          let r : ℝ := C / Real.sqrt (neff E)
          (∀ δ η : ℝ, 0 < δ → δ < Real.exp (-1) → 0 ≤ η →
            let ε : (Fin n → 𝒳 × ℝ) → ℝ≥0∞ := fun s =>
              ENNReal.ofReal r *
                ((radX (obsX s) ((fun h => f₁ ∘ h) '' H) +
                      ENNReal.ofReal BY * radX (obsX s) ((fun h => f₂ ∘ h) '' H)) *
                    ENNReal.ofReal (Real.sqrt (Real.log (1 / δ))) +
                  ENNReal.ofReal ((B₁ + BY * B₂) * Real.log (1 / δ)))
            μ {s | (∃ h ∈ H, ε s < ENNReal.ofReal |Lhat h s - L h|) ∨
                (∃ ĥ ∈ H, Lhat ĥ s ≤ sInf ((fun h => Lhat h s) '' H) + η ∧
                  2 * ε s + ENNReal.ofReal η < ENNReal.ofReal (L ĥ - sInf (L '' H)))} ≤
              ENNReal.ofReal δ) ∧
          (∀ L₁ L₂ : NNReal, LipschitzOnWith L₁ f₁ Z → LipschitzOnWith L₂ f₂ Z →
            ∀ δ η : ℝ, 0 < δ → δ < Real.exp (-1) → 0 ≤ η →
              μ {s | ∃ ĥ ∈ H, Lhat ĥ s ≤ sInf ((fun h => Lhat h s) '' H) + η ∧
                  ENNReal.ofReal r *
                      (ENNReal.ofReal ((L₁ : ℝ) + BY * (L₂ : ℝ)) * radX (obsX s) H *
                          ENNReal.ofReal (Real.sqrt (Real.log (1 / δ))) +
                        ENNReal.ofReal ((B₁ + BY * B₂) * Real.log (1 / δ))) +
                    ENNReal.ofReal η < ENNReal.ofReal (L ĥ - sInf (L '' H))} ≤
                ENNReal.ofReal δ) := by sorry

end HiddenCorr.ERM
