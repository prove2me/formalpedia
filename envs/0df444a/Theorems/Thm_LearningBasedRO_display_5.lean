-- Prove2me | Theorems.Thm_LearningBasedRO_display_5
-- name    : LearningBasedRO.display_5
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T13:31:09.804786+00:00
-- url     : https://prove2.me/theorems/9cda7f90-f95f-4d45-a30f-def95ce4789e
-- title:
--   (5) — conditional on $D_1$, $P_{D_2}(P(\xi\in U(D))\ge1-\epsilon\mid D_1)\ge1-\delta$
-- statement:
--   Let $P$ be a probability measure on a measurable space $E$, $0<\epsilon<1$, $0<\delta<1$, and $n_2\ge\log\delta/\log(1-\epsilon)$. Fix a realization $d_1$ of the Phase 1 data $D_1$, and let $t=t(d_1,\cdot):E\to\mathbb R$ be the score map built from it, measurable and such that $t(\xi)$, $\xi\sim P$, has an atomless law. Let $q_{1-\epsilon}=\inf\{y: P(t(\xi)\le y)\ge 1-\epsilon\}$ be the $(1-\epsilon)$-quantile of $t(\xi)$ and $U(D)=\{\xi: t(\xi)\le t(\xi^2_{(i^*)})\}$. Then, for $D_2=(\xi^2_1,\dots,\xi^2_{n_2})$ i.i.d. from $P$,
--
--   1. $P(\xi\in U(D))\ge 1-\epsilon$ holds exactly when $q_{1-\epsilon}\le t(\xi^2_{(i^*)})$;
--   2. $$P_{D_2}\big(P(\xi\in U(D))\ge 1-\epsilon\ \big|\ D_1=d_1\big)\ge 1-\delta .$$
--
--   This is the conditional form of the guarantee: because $t$ depends only on $D_1$, Lemma 3 applies to the scores of $D_2$ for each fixed $D_1$.
--
--   Differences from the source:
--   - reading: ϵ, δ levels (range not stated) → 0 < ϵ < 1, 0 < δ < 1; reason: the meaningful range; log(1 − ϵ) requires ϵ < 1
--   - reading: t(ξ) is a continuous random variable → the law of t(d₁, ξ), ξ ~ P, is atomless at the fixed realization d₁; reason: the weakest standard meaning; atomlessness of P itself follows, so it is not assumed separately
--   - reading: the (1 − ϵ)-quantile of t(ξ) → the lower quantile inf{y : P(t(ξ) ≤ y) ≥ 1 − ϵ}; reason: with a different quantile inside a flat stretch of the distribution function, the second equality of (5) holds only up to a null event
--   - generalization: ξ ∈ ℝᵐ and t a map constructed from D₁ → any measurable space E, only the realized map t(d₁, ·) assumed measurable; reason: (5) concerns one fixed realization; specializes to the paper's setting
--   - encoding: the conditional probability given D₁ and the chain of (5) → the P^{n₂}-measure of the section at d₁; the first identity of events (combining the two equalities, P(t(ξ) ≤ t(ξ²₍ᵢ*₎)) being P(ξ ∈ U(D)) by definition of U) and the final inequality; order statistics with multiplicity; reason: D₂ is independent of D₁, so the conditional law of D₂ is P^{n₂}
-- source:
--   Hong–Huang–Lam, arXiv:1704.04342v2, proof of Theorem 1, (5), p.9

import Mathlib
import Definitions.Def_LearningBasedRO_Model

open MeasureTheory

namespace LearningBasedRO

/-- **(5).** Conditional on any realization `d₁` of the Phase-1 data `D₁`: with `q₁₋ϵ` the
`(1 - ϵ)`-quantile of `t(ξ)`, `ξ ~ P`, the event `P(ξ ∈ U(D)) ≥ 1 - ϵ` coincides with
`q₁₋ϵ ≤ t(ξ²₍ᵢ*₎)`, and its probability over `D₂ ~ P^{n₂}` is at least `1 - δ`.
Hong–Huang–Lam, arXiv:1704.04342v2, proof of Theorem 1, (5), p.9.

**Formalization Note** Conditioning on `D₁ = d₁` is the section of the product law at `d₁`: the
probability over `D₂ ~ P^{n₂}` with `d₁` fixed. The hypotheses are those of Theorem 1 at the fixed
realization: `t d₁` measurable and `t(ξ)` atomless ("continuous"). `q₁₋ϵ` is the lower
`(1 - ϵ)`-quantile `inf{y : P(t(ξ) ≤ y) ≥ 1 - ϵ}` of the law `P ∘ (t d₁)⁻¹`. -/
theorem display_5 {E : Type*} [MeasurableSpace E] (P : Measure E) [IsProbabilityMeasure P]
    (n₁ n₂ : ℕ) (ϵ δ : ℝ) (hϵ0 : 0 < ϵ) (hϵ1 : ϵ < 1) (hδ0 : 0 < δ) (hδ1 : δ < 1)
    (hn₂ : Real.log δ / Real.log (1 - ϵ) ≤ (n₂ : ℝ)) (t : (Fin n₁ → E) → E → ℝ)
    (d₁ : Fin n₁ → E) (ht : Measurable (t d₁)) (hcont : NullSingletonClass (P.map (t d₁))) :
    {d₂ : Fin n₂ → E | IsContentSet P ϵ (uncertaintySet t ϵ δ (d₁, d₂))} =
        {d₂ : Fin n₂ → E |
          sInf {y : ℝ | ENNReal.ofReal (1 - ϵ) ≤ (P.map (t d₁)) (Set.Iic y)} ≤
            orderStat (fun i => t d₁ (d₂ i)) (iStar n₂ ϵ δ)} ∧
      ENNReal.ofReal (1 - δ) ≤
        (Measure.pi fun _ : Fin n₂ => P)
          {d₂ | IsContentSet P ϵ (uncertaintySet t ϵ δ (d₁, d₂))} := by sorry

end LearningBasedRO
