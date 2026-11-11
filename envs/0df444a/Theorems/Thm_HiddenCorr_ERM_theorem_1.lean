-- Prove2me | Theorems.Thm_HiddenCorr_ERM_theorem_1
-- name    : HiddenCorr.ERM.theorem_1
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T02:36:38.635402+00:00
-- url     : https://prove2.me/theorems/65a760c7-1107-4505-b581-e530d2584873
-- title:
--   Theorem 1 — pseudo-label ERM has excess 0-1 risk $C(\sqrt{d\log(1/\delta)}+\log(1/\delta))/\sqrt{n_{\mathrm{eff}}(G)}\le C\sqrt{|E|}/n\,(\dots)$; Natarajan classes with $d\log(nk)$
-- statement:
--   There is an absolute constant $C>0$ such that the following holds for every matching-covered candidate graph $G$ with $n$ vertices on each side, every hidden matching $M\in\mathcal M(G)$, every distribution $D$ and every $\delta\in(0,1/e)$.
--
--   (i) Let $\mathcal Y=\{0,1\}$ and let $H$ have VC dimension $d\ge1$. With probability at least $1-\delta$, pseudo-label ERM outputs $\hat h\in H$ with
--   $$L(\hat h)-\inf_{h\in H}L(h)\le\frac{C}{\sqrt{n_{\mathrm{eff}}(G)}}\Big(\sqrt{d\log\tfrac1\delta}+\log\tfrac1\delta\Big)\le\frac{C\sqrt{|E|}}{n}\Big(\sqrt{d\log\tfrac1\delta}+\log\tfrac1\delta\Big).$$
--
--   (ii) Let $\mathcal Y=[k]$ with $k\ge2$ and let $H$ have Natarajan dimension $d\ge1$. Then the same guarantee holds with $d$ replaced by $d\log(nk)$.
--
--   Here $L(h)=\Pr_{(X,Y)\sim D}(h(X)\ne Y)$ is the 0-1 risk, $n_{\mathrm{eff}}(G)=u^\top L^\dagger u$ the Laplacian energy of the bipartite demand vector, and pseudo-label ERM returns a minimizer over $H$ of the pseudo-label risk $\hat L_G$ (Eq. (42) for binary labels; $1-\frac1n\sum_i\tilde q_{i,h(X_i)}$ for $[k]$), computed from the graph and the two unlinked samples without knowledge of $M$. The theorem shows that the statistical cost of a hidden correspondence is captured by $n_{\mathrm{eff}}(G)$: pseudo-label ERM learns at the rate of ordinary ERM with $n_{\mathrm{eff}}(G)$ labeled examples, up to logarithmic factors.
--
--   **Formalization Note.** The failure probability is the (outer) measure of the set of samples on which some exact minimizer $\hat h$ of $\hat L_G$ violates the bound; minimizers always exist, because $\hat L_G(h)$ depends on $h$ only through its finitely many values $h(X_1),\dots,h(X_n)$. The second inequality is stated as a separate deterministic conjunct.
--
--   Differences from the source:
--   - encoding: [n] and the sides U, V of G; a perfect matching M ∈ M(G) as a bijection U → V → Fin n, U ∪ V as Fin n ⊕ Fin n, E : Finset (Fin n × Fin n), a perfect matching as σ : Equiv.Perm (Fin n) with (i, σ i) ∈ E for all i; reason: Lean convention; the same graphs and matchings
--   - encoding: n vertices on each side (n ≥ 1 implicit: [n] indexes the sample) → hypothesis 0 < n; reason: excludes only the empty sample, where 1/√n_eff(G) is undefined (Lean would read 1/√0 = 0)
--   - encoding: the true pairs (X_i, Y_M(i)) are i.i.d. from D; the learner sees the unlinked X_1..X_n, Y_1..Y_n and G → a sample s : Fin n → X × Y drawn from Measure.pi (fun _ => D); observed X_i = (s i).1, Y_j = (s (σ⁻¹ j)).2; the learner's statistic uses E, X, Y only; reason: the paper's data-independent model (§4.1), written out
--   - encoding: Y = {0, 1}, hypotheses h : X → {0, 1} → labels and hypotheses Bool-valued; the real value b2r b ∈ {0, 1} enters the pseudo-label risk; reason: same objects
--   - encoding: H has VC dimension d → NatureSLT.GrowthFunction.vcDim of the family (h : ↥H) ↦ h equals (d : ℕ∞); reason: published VC dimension; finite d as printed
--   - encoding: Y = [k] ≅ {e_1, …, e_k}, hypotheses with values in {e_1, …, e_k} → labels and hypotheses Fin k-valued; one-hot vectors onehot r = e_r in the losses and pseudo-labels; reason: same objects
--   - encoding: H has (finite) Natarajan dimension d → MulticlassDS.NatGap.natarajanDim H = (d : ℕ∞); reason: published Natarajan dimension (sequences with f(i) ≠ g(i)); same value as for sets
--   - reading: footnote 1 (p. 13): all functions, learning rules and suprema over function classes are measurable → the relevant functions are Measurable and the class is pointwise measurable (countable dense subclass in the pointwise sense: published IsPointwiseMeasurableClass, or its vector version IsPointwiseMeasurableClassV); reason: standard reading of the measurability convention; it makes every supremum in the statement equal to a countable one
--   - encoding: H is a nonempty class → no separate nonemptiness hypothesis; reason: dimension d ≥ 1 already forces H ≠ ∅ (the empty class has dimension 0), so the hypothesis would be redundant (trap 36)
--   - encoding: with probability at least 1 − δ, … → the measure (outer measure) of the set of samples on which the claim fails is ≤ ENNReal.ofReal δ; reason: avoids requiring the failure event to be measurable; equivalent when it is measurable
--   - encoding: log, natural logarithm; δ ∈ (0, 1/e) → Real.log; 0 < δ ∧ δ < Real.exp (-1); reason: same
--   - reading: 'with probability at least 1 − δ, pseudo-label ERM outputs ĥ ∈ H with …' (no tolerance η) → every exact minimizer ĥ ∈ H of L̂_G (∀ h ∈ H, L̂_G(ĥ) ≤ L̂_G(h)) satisfies the bound outside a set of samples of measure ≤ δ; reason: the η = 0 rule of Eq. (36); stating it for every minimizer covers any tie-breaking, and minimizers exist
--   - encoding: the chain a ≤ b of the display → a conjunction: the probability bound with the n_eff form, and the deterministic inequality C/√n_eff(G)·(…) ≤ C√|E|/n·(…); reason: the second inequality does not depend on the sample
-- source:
--   Chen, Gentile, Kaplan, Koren, Supervised Learning with Hidden Correspondences, STOC 2027 submission (manuscript sha256 d0029978…), p. 4, Theorem 1 (proved p. 4 from Theorems 9 and 11, Lemma 1)

import Mathlib
import Definitions.Def_IncrementalER_energy
import Definitions.Def_NatureSLT_GrowthFunction_vcDim
import Definitions.Def_MulticlassDS_NatGap_Dimensions
import Definitions.Def_BartlettBousquetMendelson_LocalRad_IsPointwiseMeasurableClass
import Definitions.Def_HiddenCorr_ERM_CandidateGraph
import Definitions.Def_HiddenCorr_ERM_Complexity
import Definitions.Def_HiddenCorr_ERM_PseudoLabel

open MeasureTheory
open scoped ENNReal

universe u

namespace HiddenCorr.ERM

/-- **Theorem 1** (agnostic learning with 0-1 loss), p. 4. There is an absolute constant `C > 0`
such that for every matching-covered candidate graph `G` with `n ≥ 1` vertices on each side, every
hidden matching `σ ∈ M(G)`, every distribution `D` and every `δ ∈ (0, 1/e)`:
(i) for `Y = {0, 1}` and a (pointwise measurable) class `H` of measurable hypotheses with VC
dimension `d ≥ 1`, the probability of the set of samples on which some exact minimizer `ĥ ∈ H` of
the pseudo-label risk `L̂_G` has `L(ĥ) − inf_H L > (C/√n_eff(G)) (√(d log(1/δ)) + log(1/δ))` is at
most `δ`, and `(C/√n_eff(G)) (…) ≤ (C √|E| / n) (…)`;
(ii) for `Y = [k]`, `k ≥ 2`, and a (pointwise measurable) class of measurable hypotheses with
Natarajan dimension `d ≥ 1`, the same holds with `d` replaced by `d log(nk)`. -/
theorem theorem_1 :
    ∃ C : ℝ, 0 < C ∧
      ∀ {𝒳 : Type u} [MeasurableSpace 𝒳] (n : ℕ), 0 < n →
        ∀ (E : Finset (Fin n × Fin n)) (σ : Equiv.Perm (Fin n)),
        MatchingCovered E → IsPerfectMatching E σ →
        ∀ δ : ℝ, 0 < δ → δ < Real.exp (-1) →
          (∀ (D : Measure (𝒳 × Bool)) [IsProbabilityMeasure D] (H : Set (𝒳 → Bool)) (d : ℕ),
            1 ≤ d → NatureSLT.GrowthFunction.vcDim (fun h : H => (h : 𝒳 → Bool)) = d →
            (∀ h ∈ H, Measurable h) →
            BartlettBousquetMendelson.LocalRad.IsPointwiseMeasurableClass
              ((fun h x => b2r (h x)) '' H) →
              let rate : ℝ := Real.sqrt (d * Real.log (1 / δ)) + Real.log (1 / δ)
              let Lhat : (𝒳 → Bool) → (Fin n → 𝒳 × Bool) → ℝ := fun h s =>
                pseudoRisk01 E h (obsX s) (obsY σ s)
              (Measure.pi fun _ : Fin n => D)
                  {s | ∃ ĥ ∈ H, (∀ h ∈ H, Lhat ĥ s ≤ Lhat h s) ∧
                    C / Real.sqrt (neff E) * rate <
                      risk01 D ĥ - sInf ((fun h => risk01 D h) '' H)} ≤ ENNReal.ofReal δ ∧
                C / Real.sqrt (neff E) * rate ≤ C * Real.sqrt (E.card : ℝ) / n * rate) ∧
          (∀ (k : ℕ), 2 ≤ k →
            ∀ (D : Measure (𝒳 × Fin k)) [IsProbabilityMeasure D] (H : Set (𝒳 → Fin k)) (d : ℕ),
            1 ≤ d → MulticlassDS.NatGap.natarajanDim H = d →
            (∀ h ∈ H, Measurable h) →
            BartlettBousquetMendelson.LocalRad.IsPointwiseMeasurableClass
              ((fun h x => ((h x : ℕ) : ℝ)) '' H) →
              let rate : ℝ :=
                Real.sqrt (d * Real.log ((n : ℝ) * k) * Real.log (1 / δ)) + Real.log (1 / δ)
              let Lhat : (𝒳 → Fin k) → (Fin n → 𝒳 × Fin k) → ℝ := fun h s =>
                pseudoRiskMulti01 E h (obsX s) (obsY σ s)
              (Measure.pi fun _ : Fin n => D)
                  {s | ∃ ĥ ∈ H, (∀ h ∈ H, Lhat ĥ s ≤ Lhat h s) ∧
                    C / Real.sqrt (neff E) * rate <
                      risk01 D ĥ - sInf ((fun h => risk01 D h) '' H)} ≤ ENNReal.ofReal δ ∧
                C / Real.sqrt (neff E) * rate ≤ C * Real.sqrt (E.card : ℝ) / n * rate) := by sorry

end HiddenCorr.ERM
