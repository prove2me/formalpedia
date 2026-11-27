-- Prove2me | Theorems.Thm_LearningBasedRO_Supplement_theorem_2
-- name    : LearningBasedRO.Supplement.theorem_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-27T02:16:41.505918+00:00
-- url     : https://prove2.me/theorems/836e1024-f98c-4ef3-a4af-3cc76ceab8a7
-- title:
--   Theorem 2 — asymptotic tightness: given $D_1$, $P(\xi\in U)\to1-\epsilon$ in probability and $P_{D_2}(P(\xi\in U)\ge1-\epsilon\mid D_1)\to1-\delta$
-- statement:
--   Let $P$ be a probability measure on a measurable space $E$, $0<\epsilon<1$ and $0<\delta<1$. Fix $n_1$ and a realization $d_1$ of the Phase 1 data $D_1$, and let $t=t(d_1,\cdot):E\to\mathbb R$ be the score map built from it, measurable and such that $t(\xi)$, $\xi\sim P$, is a continuous (atomless) random variable. For each $n_2$ let $D_2=(\xi^2_1,\dots,\xi^2_{n_2})$ be i.i.d. from $P$ and
--   $$U=\{\xi:\ t(\xi)\le t(\xi^2_{(i^*)})\}$$
--   with $i^*$ of (4). Then, conditional on $D_1=d_1$, as $n_2\to\infty$:
--
--   1. $P(\xi\in U)\to1-\epsilon$ in probability with respect to $D_2$: for every $\gamma>0$,
--   $$P_{D_2}\big(|P(\xi\in U)-(1-\epsilon)|>\gamma\ \big|\ D_1\big)\to0;$$
--   2. $$P_{D_2}\big(P(\xi\in U)\ge1-\epsilon\ \big|\ D_1\big)\to1-\delta .$$
--
--   Theorem 1 guarantees tolerance $1-\epsilon$ with confidence at least $1-\delta$; Theorem 2 shows that neither level is conservative in the limit, which is Criterion 2 of §2.1.
--
--   **Formalization Note** Conditioning on $D_1$ is the section at $d_1$, with $D_2\sim P^{n_2}$; $n_1$ and $d_1$ stay fixed. The coverage $P(\xi\in U)$ is used as a real number in part 1.
--
--   Differences from the source:
--   - reading: ϵ, δ levels (range not stated in the theorem) → 0 < ϵ < 1, 0 < δ < 1; reason: the paper's standing range (p.1, p.5); log(1 − ϵ) and the quantiles need it
--   - reading: t(ξ), ξ ~ P, is a continuous random variable → the law of t(d₁, ξ), ξ ~ P, is atomless (NullSingletonClass) at the fixed realization d₁, and t(d₁, ·) is measurable; reason: the weakest standard meaning, as in the published (5); atomlessness of P follows and is not assumed separately
--   - generalization: ξ ∈ ℝᵐ, P a continuous distribution, t a map constructed from D₁, assumptions for every D₁ → any measurable space E, any probability measure P, hypotheses only at the fixed realization d₁; reason: the statement is conditional on D₁ = d₁; under Theorem 1's assumptions every d₁ satisfies the hypotheses, so it specializes to the paper's setting
--   - encoding: conditional on D₁ → the section at a fixed realization d₁, D₂ ~ P^{n₂} (Measure.pi); reason: D₂ is independent of D₁, so the conditional law of D₂ is P^{n₂}; same encoding as the published (5)
--   - encoding: the sample-size condition n₂ ≥ log δ / log(1 − ϵ) among 'the same assumptions as in Theorem 1' → omitted; reason: it holds for all large n₂, and a limit as n₂ → ∞ depends only on large n₂
--   - encoding: P(ξ ∈ U) → 1 − ϵ in probability (with respect to D₂) → for every γ > 0, P^{n₂}{d₂ : |P(U(d₁, d₂)) − (1 − ϵ)| > γ} → 0; reason: the definition of convergence in probability, written out because the sample space E^{n₂} changes with n₂
--   - encoding: ranked observations t(ξ²₍₁₎) < ⋯ < t(ξ²₍ₙ₂₎) → order statistics with multiplicity (base orderStat); reason: ties have probability zero under the atomless hypothesis
-- source:
--   Hong–Huang–Lam, arXiv:1704.04342v2, Theorem 2, p.10 (proof Appendix EC.1, pp.ec1–ec3)

import Mathlib
import Definitions.Def_LearningBasedRO_Model

open MeasureTheory Filter Topology

namespace LearningBasedRO.Supplement

/-- **Theorem 2 (Asymptotic tightness of tolerance and confidence levels).** Under the same
assumptions as in Theorem 1, conditional on `D₁`:
1. `P(ξ ∈ U) → 1 - ϵ` in probability (with respect to `D₂`) as `n₂ → ∞`;
2. `P_{D₂}(P(ξ ∈ U) ≥ 1 - ϵ | D₁) → 1 - δ` as `n₂ → ∞`.
Hong–Huang–Lam, arXiv:1704.04342v2, Theorem 2, p.10 (proof Appendix EC.1, pp.ec1–ec3).

**Formalization Note** "Conditional on `D₁`" is the section at a fixed realization `d₁` (as in the
base mission's (5)); `n₁` and `d₁` are fixed and only `n₂` grows, with `D₂ ~ P^{n₂}`
(`Measure.pi`). The hypotheses are Theorem 1's at `d₁`: `t d₁` measurable and `t(ξ)`, `ξ ~ P`,
atomless ("continuous"); `0 < ϵ, δ < 1`. Theorem 1's sample-size condition
`n₂ ≥ log δ / log(1 - ϵ)` holds for all large `n₂` and cannot affect a limit, so it is omitted.
Convergence in probability on the changing sample spaces `E^{n₂}` is written out: for every
`γ > 0`, `P^{n₂}(|P(U) - (1 - ϵ)| > γ) → 0`. The coverage `P(U)` is used as a real number. -/
theorem theorem_2 {E : Type*} [MeasurableSpace E] (P : Measure E) [IsProbabilityMeasure P]
    (n₁ : ℕ) (ϵ δ : ℝ) (hϵ0 : 0 < ϵ) (hϵ1 : ϵ < 1) (hδ0 : 0 < δ) (hδ1 : δ < 1)
    (t : (Fin n₁ → E) → E → ℝ) (d₁ : Fin n₁ → E) (ht : Measurable (t d₁))
    (hcont : NullSingletonClass (P.map (t d₁))) :
    (∀ γ : ℝ, 0 < γ →
      Tendsto (fun n₂ : ℕ => (Measure.pi fun _ : Fin n₂ => P)
          {d₂ : Fin n₂ → E | γ < |(P (uncertaintySet t ϵ δ (d₁, d₂))).toReal - (1 - ϵ)|})
        atTop (𝓝 0)) ∧
      Tendsto (fun n₂ : ℕ => (Measure.pi fun _ : Fin n₂ => P)
          {d₂ : Fin n₂ → E | IsContentSet P ϵ (uncertaintySet t ϵ δ (d₁, d₂))})
        atTop (𝓝 (ENNReal.ofReal (1 - δ))) := by sorry

end LearningBasedRO.Supplement
