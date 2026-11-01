-- Prove2me | Theorems.Thm_LearningBasedRO_requirement_3
-- name    : LearningBasedRO.requirement_3
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T13:30:55.760473+00:00
-- url     : https://prove2.me/theorems/80ab9086-ef11-4620-9d83-3a850e75b97e
-- title:
--   Display after (5) — averaging over $D_1$, $U(D)$ satisfies (3)
-- statement:
--   Let $P$ be a probability measure on a measurable space $E$, $0<\epsilon<1$, $0<\delta<1$, $n_1\ge 0$ and $n_2\ge\log\delta/\log(1-\epsilon)$. Let $D=(D_1,D_2)$ be the split sample with law $P^{n_1}\otimes P^{n_2}$, and $t(D_1,\xi)$ a score map, jointly measurable in $(D_1,\xi)$, such that for every realization of $D_1$ the law of $t(D_1,\xi)$, $\xi\sim P$, is atomless. Let $U(D)=\{\xi: t(D_1,\xi)\le t(D_1,\xi^2_{(i^*)})\}$. Then the event $\{P(\xi\in U(D))\ge 1-\epsilon\}$ is measurable,
--   $$\mathbb E_{D_1}\Big[P_{D_2}\big(P(\xi\in U(D))\ge 1-\epsilon\ \big|\ D_1\big)\Big]\ge 1-\delta,$$
--   this expectation equals $P_D\big(P(\xi\in U(D))\ge 1-\epsilon\big)$, and hence
--   $$P_D\big(P(\xi\in U(D))\ge 1-\epsilon\big)\ge 1-\delta,$$
--   i.e. $U$ satisfies requirement (3).
--
--   This is the unconditional coverage guarantee of the learned uncertainty set; with Lemma 2 it gives the feasibility statement of Theorem 1.
--
--   Differences from the source:
--   - reading: ϵ, δ levels (range not stated) → 0 < ϵ < 1, 0 < δ < 1; reason: the meaningful range; log(1 − ϵ) requires ϵ < 1
--   - reading: t(ξ) is a continuous random variable → the law of t(d₁, ξ), ξ ~ P, is atomless for every realization d₁; reason: the weakest standard meaning; atomlessness of P itself follows, so it is not assumed separately
--   - reading: t a map constructed from D₁ → a jointly measurable function t(D₁, ξ); reason: the probabilities over D of events built from t presume measurability; t never depends on D₂
--   - generalization: ξ ∈ ℝᵐ → any measurable space E; reason: the paper's case is E = ℝᵐ
--   - encoding: the i.i.d. data set partitioned into D₁ and D₂, E_{D₁}[P_{D₂}(· | D₁)] → the product law P^{n₁} ⊗ P^{n₂}, the lower Lebesgue integral over P^{n₁} of the P^{n₂}-measure of the section; the measurability of the event as a conclusion; order statistics with multiplicity; reason: the partition is fixed in advance, so (D₁, D₂) has the product law and the conditional law of D₂ given D₁ is P^{n₂}
-- source:
--   Hong–Huang–Lam, arXiv:1704.04342v2, proof of Theorem 1, display after (5), p.9

import Mathlib
import Definitions.Def_LearningBasedRO_Model

open MeasureTheory

namespace LearningBasedRO

/-- **Display after (5).** Averaging (5) over the Phase-1 data:
`E_{D₁}[P_{D₂}(P(ξ ∈ U(D)) ≥ 1 - ϵ | D₁)] ≥ 1 - δ`, which gives
`P_D(P(ξ ∈ U(D)) ≥ 1 - ϵ) ≥ 1 - δ`, i.e. `U` satisfies (3).
Hong–Huang–Lam, arXiv:1704.04342v2, proof of Theorem 1, display after (5), p.9.

**Formalization Note** The split sample `D = (D₁, D₂)` has law `P^{n₁} ⊗ P^{n₂}` (`splitLaw`); the
conditional probability given `D₁ = d₁` is the `P^{n₂}`-measure of the section at `d₁`, and
`E_{D₁}` is the lower Lebesgue integral against `P^{n₁}`. The event of (3) is shown measurable,
so its probability is a genuine measure, not an outer-measure value. "Continuous" is read as
atomless for every realization of `D₁`; `t` is jointly measurable in `(D₁, ξ)`. -/
theorem requirement_3 {E : Type*} [MeasurableSpace E] (P : Measure E) [IsProbabilityMeasure P]
    (n₁ n₂ : ℕ) (ϵ δ : ℝ) (hϵ0 : 0 < ϵ) (hϵ1 : ϵ < 1) (hδ0 : 0 < δ) (hδ1 : δ < 1)
    (hn₂ : Real.log δ / Real.log (1 - ϵ) ≤ (n₂ : ℝ)) (t : (Fin n₁ → E) → E → ℝ)
    (ht : Measurable (Function.uncurry t)) (hcont : ∀ d₁, NullSingletonClass (P.map (t d₁))) :
    MeasurableSet {D : (Fin n₁ → E) × (Fin n₂ → E) | IsContentSet P ϵ (uncertaintySet t ϵ δ D)} ∧
      ENNReal.ofReal (1 - δ) ≤
        ∫⁻ d₁, (Measure.pi fun _ : Fin n₂ => P)
            {d₂ | IsContentSet P ϵ (uncertaintySet t ϵ δ (d₁, d₂))}
          ∂(Measure.pi fun _ : Fin n₁ => P) ∧
      splitLaw P n₁ n₂ {D | IsContentSet P ϵ (uncertaintySet t ϵ δ D)} =
        ∫⁻ d₁, (Measure.pi fun _ : Fin n₂ => P)
            {d₂ | IsContentSet P ϵ (uncertaintySet t ϵ δ (d₁, d₂))}
          ∂(Measure.pi fun _ : Fin n₁ => P) ∧
      SatisfiesReq3 (splitLaw P n₁ n₂) P ϵ δ (uncertaintySet t ϵ δ) := by sorry

end LearningBasedRO
