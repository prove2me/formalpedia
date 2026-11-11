-- Prove2me | Theorems.Thm_HiddenCorr_ERM_theorem_11
-- name    : HiddenCorr.ERM.theorem_11
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T02:36:38.115663+00:00
-- url     : https://prove2.me/theorems/8b076a37-be7b-417b-95fc-c0f9f205f48b
-- title:
--   Theorem 11 — multiclass classification: uniform accuracy (52) and excess risk, $C(\sqrt{d\log(nk)\log(1/\delta)}+\log(1/\delta))/\sqrt{u^\top L^\dagger u}$
-- statement:
--   There is an absolute constant $C>0$ such that the following holds. Let $k\ge2$; fix a matching-covered graph $G$ with $n$ vertices on each side and a hidden matching $M\in\mathcal M(G)$, independent of the data; the true pairs are i.i.d. from any $D$ on $\mathcal X\times[k]$; $L$ is the multiclass 0-1 risk and $H$ a class of hypotheses $\mathcal X\to[k]$ (one-hot predictors) of finite Natarajan dimension $d\ge1$. For every $\delta\in(0,1/e)$ and $\eta\ge0$, with probability at least $1-\delta$,
--   $$\sup_{h\in H}|\hat L_G(h)-L(h)|\le\frac{C}{\sqrt{u^\top L^\dagger u}}\Big(\sqrt{d\log(nk)\log\tfrac1\delta}+\log\tfrac1\delta\Big)\qquad\text{(52)},$$
--   and on the same event every output $\hat h$ satisfying Eq. (47) obeys
--   $$L(\hat h)-\inf_{h\in H}L(h)\le\frac{C}{\sqrt{u^\top L^\dagger u}}\Big(\sqrt{d\log(nk)\log\tfrac1\delta}+\log\tfrac1\delta\Big)+\eta.$$
--   Here $\hat L_G(h)=1-\frac1n\sum_i\tilde q_{i,h(X_i)}$, the 0-1 instance $f_1=1$, $f_2(z)=-z$ of Eq. (46).
--
--   Differences from the source:
--   - encoding: [n] and the sides U, V of G; a perfect matching M ∈ M(G) as a bijection U → V → Fin n, U ∪ V as Fin n ⊕ Fin n, E : Finset (Fin n × Fin n), a perfect matching as σ : Equiv.Perm (Fin n) with (i, σ i) ∈ E for all i; reason: Lean convention; the same graphs and matchings
--   - encoding: n vertices on each side (n ≥ 1 implicit: [n] indexes the sample) → hypothesis 0 < n; reason: excludes only the empty sample, where 1/√n_eff(G) is undefined (Lean would read 1/√0 = 0)
--   - encoding: the true pairs (X_i, Y_M(i)) are i.i.d. from D; the learner sees the unlinked X_1..X_n, Y_1..Y_n and G → a sample s : Fin n → X × Y drawn from Measure.pi (fun _ => D); observed X_i = (s i).1, Y_j = (s (σ⁻¹ j)).2; the learner's statistic uses E, X, Y only; reason: the paper's data-independent model (§4.1), written out
--   - encoding: Y = [k] ≅ {e_1, …, e_k}, hypotheses with values in {e_1, …, e_k} → labels and hypotheses Fin k-valued; one-hot vectors onehot r = e_r in the losses and pseudo-labels; reason: same objects
--   - encoding: H has (finite) Natarajan dimension d → MulticlassDS.NatGap.natarajanDim H = (d : ℕ∞); reason: published Natarajan dimension (sequences with f(i) ≠ g(i)); same value as for sets
--   - reading: footnote 1 (p. 13): all functions, learning rules and suprema over function classes are measurable → the relevant functions are Measurable and the class is pointwise measurable (countable dense subclass in the pointwise sense: published IsPointwiseMeasurableClass, or its vector version IsPointwiseMeasurableClassV); reason: standard reading of the measurability convention; it makes every supremum in the statement equal to a countable one
--   - encoding: H is a nonempty class → no separate nonemptiness hypothesis; reason: dimension d ≥ 1 already forces H ≠ ∅ (the empty class has dimension 0), so the hypothesis would be redundant (trap 36)
--   - encoding: with probability at least 1 − δ, … → the measure (outer measure) of the set of samples on which the claim fails is ≤ ENNReal.ofReal δ; reason: avoids requiring the failure event to be measurable; equivalent when it is measurable
--   - reading: on the same event, any output ĥ satisfying the η-ERM rule obeys the excess-risk bound → one failure set: the uniform-deviation bound fails for some h, or some η-minimizer ĥ violates the excess-risk bound; its measure is ≤ δ (η ≥ 0 fixed first); reason: this is what 'on the same event' asserts
--   - encoding: log, natural logarithm; δ ∈ (0, 1/e) → Real.log; 0 < δ ∧ δ < Real.exp (-1); reason: same
-- source:
--   Chen, Gentile, Kaplan, Koren, Supervised Learning with Hidden Correspondences, STOC 2027 submission (manuscript sha256 d0029978…), p. 32, Theorem 11, Eq. (52)

import Mathlib
import Definitions.Def_IncrementalER_energy
import Definitions.Def_MulticlassDS_NatGap_Dimensions
import Definitions.Def_BartlettBousquetMendelson_LocalRad_IsPointwiseMeasurableClass
import Definitions.Def_HiddenCorr_ERM_CandidateGraph
import Definitions.Def_HiddenCorr_ERM_Complexity
import Definitions.Def_HiddenCorr_ERM_PseudoLabel

open MeasureTheory
open scoped ENNReal

universe u

namespace HiddenCorr.ERM

/-- **Theorem 11** (learning guarantee for multiclass classification), p. 32. There is an absolute
constant `C > 0` such that: let `k ≥ 2`; fix a matching-covered candidate graph `G` with `n ≥ 1`
vertices on each side and a hidden perfect matching `σ`, independent of the data; the true pairs
are i.i.d. from any `D` on `X × [k]`; `L` is the multiclass 0-1 risk; `H` is a (pointwise
measurable) class of measurable `h : X → [k]` (one-hot predictors) with finite Natarajan dimension
`d ≥ 1`. For every `δ ∈ (0, 1/e)` and `η ≥ 0`, with probability at least `1 − δ`,
`sup_{h ∈ H} |L̂_G(h) − L(h)| ≤ (C/√(uᵀL†u)) (√(d log(nk) log(1/δ)) + log(1/δ))` (Eq. (52)), and on
the same event every `ĥ` satisfying Eq. (47) obeys
`L(ĥ) − inf_H L ≤ (C/√(uᵀL†u)) (√(d log(nk) log(1/δ)) + log(1/δ)) + η`. -/
theorem theorem_11 :
    ∃ C : ℝ, 0 < C ∧
      ∀ {𝒳 : Type u} [MeasurableSpace 𝒳] (k : ℕ), 2 ≤ k → ∀ (n : ℕ), 0 < n →
        ∀ (E : Finset (Fin n × Fin n)) (σ : Equiv.Perm (Fin n)),
        MatchingCovered E → IsPerfectMatching E σ →
        ∀ (D : Measure (𝒳 × Fin k)) [IsProbabilityMeasure D] (H : Set (𝒳 → Fin k)) (d : ℕ),
        1 ≤ d → MulticlassDS.NatGap.natarajanDim H = d →
        (∀ h ∈ H, Measurable h) →
        BartlettBousquetMendelson.LocalRad.IsPointwiseMeasurableClass
          ((fun h x => ((h x : ℕ) : ℝ)) '' H) →
        ∀ δ η : ℝ, 0 < δ → δ < Real.exp (-1) → 0 ≤ η →
          let ε : ℝ := C / Real.sqrt (neff E) *
            (Real.sqrt (d * Real.log ((n : ℝ) * k) * Real.log (1 / δ)) + Real.log (1 / δ))
          let Lhat : (𝒳 → Fin k) → (Fin n → 𝒳 × Fin k) → ℝ := fun h s =>
            pseudoRiskMulti01 E h (obsX s) (obsY σ s)
          (Measure.pi fun _ : Fin n => D)
              {s | (∃ h ∈ H, ε < |Lhat h s - risk01 D h|) ∨
                (∃ ĥ ∈ H, Lhat ĥ s ≤ sInf ((fun h => Lhat h s) '' H) + η ∧
                  ε + η < risk01 D ĥ - sInf ((fun h => risk01 D h) '' H))} ≤
            ENNReal.ofReal δ := by sorry

end HiddenCorr.ERM
