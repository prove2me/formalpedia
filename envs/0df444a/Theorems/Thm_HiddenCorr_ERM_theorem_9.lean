-- Prove2me | Theorems.Thm_HiddenCorr_ERM_theorem_9
-- name    : HiddenCorr.ERM.theorem_9
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T02:36:27.726673+00:00
-- url     : https://prove2.me/theorems/a1554f56-e89f-4f67-bbd4-00b13dc71550
-- title:
--   Theorem 9 — binary classification: uniform accuracy (43) and excess risk (44) of pseudo-label ERM, $C(\sqrt{d\log(1/\delta)}+\log(1/\delta))/\sqrt{u^\top L^\dagger u}$
-- statement:
--   There is an absolute constant $C>0$ such that the following holds. Let $\mathcal Y=\{0,1\}$, let $L$ be the 0-1 risk, and let $H$ be a class of functions $h:\mathcal X\to\{0,1\}$ with VC dimension $d\ge1$. Fix a matching-covered graph $G$ with $n$ vertices on each side and a hidden matching $M\in\mathcal M(G)$, independent of the data, and any distribution $D$ on $\mathcal X\times\{0,1\}$. For every $\delta\in(0,1/e)$ and tolerance $\eta\ge0$, with probability at least $1-\delta$,
--   $$\sup_{h\in H}\big|\hat L_G(h)-L(h)\big|\le\frac{C}{\sqrt{u^\top L^\dagger u}}\Big(\sqrt{d\log\tfrac1\delta}+\log\tfrac1\delta\Big)\qquad\text{(43)},$$
--   and on the same event every $\hat h\in H$ with $\hat L_G(\hat h)\le\inf_{h\in H}\hat L_G(h)+\eta$ obeys
--   $$L(\hat h)-\inf_{h\in H}L(h)\le\frac{C}{\sqrt{u^\top L^\dagger u}}\Big(\sqrt{d\log\tfrac1\delta}+\log\tfrac1\delta\Big)+\eta\qquad\text{(44)}.$$
--   Here $\hat L_G(h)=\frac1n\sum_i[h(X_i)+(1-2h(X_i))\tilde Y_i]$ (Eq. (42)).
--
--   Differences from the source:
--   - encoding: [n] and the sides U, V of G; a perfect matching M ∈ M(G) as a bijection U → V → Fin n, U ∪ V as Fin n ⊕ Fin n, E : Finset (Fin n × Fin n), a perfect matching as σ : Equiv.Perm (Fin n) with (i, σ i) ∈ E for all i; reason: Lean convention; the same graphs and matchings
--   - encoding: n vertices on each side (n ≥ 1 implicit: [n] indexes the sample) → hypothesis 0 < n; reason: excludes only the empty sample, where 1/√n_eff(G) is undefined (Lean would read 1/√0 = 0)
--   - encoding: the true pairs (X_i, Y_M(i)) are i.i.d. from D; the learner sees the unlinked X_1..X_n, Y_1..Y_n and G → a sample s : Fin n → X × Y drawn from Measure.pi (fun _ => D); observed X_i = (s i).1, Y_j = (s (σ⁻¹ j)).2; the learner's statistic uses E, X, Y only; reason: the paper's data-independent model (§4.1), written out
--   - encoding: Y = {0, 1}, hypotheses h : X → {0, 1} → labels and hypotheses Bool-valued; the real value b2r b ∈ {0, 1} enters the pseudo-label risk; reason: same objects
--   - encoding: H has VC dimension d → NatureSLT.GrowthFunction.vcDim of the family (h : ↥H) ↦ h equals (d : ℕ∞); reason: published VC dimension; finite d as printed
--   - reading: footnote 1 (p. 13): all functions, learning rules and suprema over function classes are measurable → the relevant functions are Measurable and the class is pointwise measurable (countable dense subclass in the pointwise sense: published IsPointwiseMeasurableClass, or its vector version IsPointwiseMeasurableClassV); reason: standard reading of the measurability convention; it makes every supremum in the statement equal to a countable one
--   - encoding: H is a nonempty class → no separate nonemptiness hypothesis; reason: dimension d ≥ 1 already forces H ≠ ∅ (the empty class has dimension 0), so the hypothesis would be redundant (trap 36)
--   - encoding: with probability at least 1 − δ, … → the measure (outer measure) of the set of samples on which the claim fails is ≤ ENNReal.ofReal δ; reason: avoids requiring the failure event to be measurable; equivalent when it is measurable
--   - reading: on the same event, any output ĥ satisfying the η-ERM rule obeys the excess-risk bound → one failure set: the uniform-deviation bound fails for some h, or some η-minimizer ĥ violates the excess-risk bound; its measure is ≤ δ (η ≥ 0 fixed first); reason: this is what 'on the same event' asserts
--   - encoding: log, natural logarithm; δ ∈ (0, 1/e) → Real.log; 0 < δ ∧ δ < Real.exp (-1); reason: same
-- source:
--   Chen, Gentile, Kaplan, Koren, Supervised Learning with Hidden Correspondences, STOC 2027 submission (manuscript sha256 d0029978…), p. 28, Theorem 9, Eqs. (43)–(44) (proof p. 29)

import Mathlib
import Definitions.Def_IncrementalER_energy
import Definitions.Def_NatureSLT_GrowthFunction_vcDim
import Definitions.Def_BartlettBousquetMendelson_LocalRad_IsPointwiseMeasurableClass
import Definitions.Def_HiddenCorr_ERM_CandidateGraph
import Definitions.Def_HiddenCorr_ERM_Complexity
import Definitions.Def_HiddenCorr_ERM_PseudoLabel

open MeasureTheory
open scoped ENNReal

universe u

namespace HiddenCorr.ERM

/-- **Theorem 9** (learning guarantee for binary classification), p. 28. There is an absolute
constant `C > 0` such that: fix a matching-covered candidate graph `G` with `n ≥ 1` vertices on each
side and a hidden perfect matching `σ`, independent of the data; the true pairs are i.i.d. from any
`D` on `X × {0, 1}`; `L` is the 0-1 risk; `H` is a (pointwise measurable) class of measurable
`h : X → {0, 1}` with VC dimension `d ≥ 1`. For every `δ ∈ (0, 1/e)` and tolerance `η ≥ 0`, with
probability at least `1 − δ`,
`sup_{h ∈ H} |L̂_G(h) − L(h)| ≤ (C/√(uᵀL†u)) (√(d log(1/δ)) + log(1/δ))` (Eq. (43)), and on the
same event every `ĥ ∈ H` with `L̂_G(ĥ) ≤ inf_H L̂_G + η` (Eq. (36)) obeys
`L(ĥ) − inf_H L ≤ (C/√(uᵀL†u)) (√(d log(1/δ)) + log(1/δ)) + η` (Eq. (44)). -/
theorem theorem_9 :
    ∃ C : ℝ, 0 < C ∧
      ∀ {𝒳 : Type u} [MeasurableSpace 𝒳] (n : ℕ), 0 < n →
        ∀ (E : Finset (Fin n × Fin n)) (σ : Equiv.Perm (Fin n)),
        MatchingCovered E → IsPerfectMatching E σ →
        ∀ (D : Measure (𝒳 × Bool)) [IsProbabilityMeasure D] (H : Set (𝒳 → Bool)) (d : ℕ),
        1 ≤ d → NatureSLT.GrowthFunction.vcDim (fun h : H => (h : 𝒳 → Bool)) = d →
        (∀ h ∈ H, Measurable h) →
        BartlettBousquetMendelson.LocalRad.IsPointwiseMeasurableClass
          ((fun h x => b2r (h x)) '' H) →
        ∀ δ η : ℝ, 0 < δ → δ < Real.exp (-1) → 0 ≤ η →
          let ε : ℝ := C / Real.sqrt (neff E) *
            (Real.sqrt (d * Real.log (1 / δ)) + Real.log (1 / δ))
          let Lhat : (𝒳 → Bool) → (Fin n → 𝒳 × Bool) → ℝ := fun h s =>
            pseudoRisk01 E h (obsX s) (obsY σ s)
          (Measure.pi fun _ : Fin n => D)
              {s | (∃ h ∈ H, ε < |Lhat h s - risk01 D h|) ∨
                (∃ ĥ ∈ H, Lhat ĥ s ≤ sInf ((fun h => Lhat h s) '' H) + η ∧
                  ε + η < risk01 D ĥ - sInf ((fun h => risk01 D h) '' H))} ≤
            ENNReal.ofReal δ := by sorry

end HiddenCorr.ERM
