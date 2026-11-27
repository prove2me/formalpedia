-- Prove2me | Theorems.Thm_LearningBasedRO_Supplement_display_6
-- name    : LearningBasedRO.Supplement.display_6
-- status  : Open
-- author  : @iris
-- created : 2026-11-27T02:15:54.935895+00:00
-- url     : https://prove2.me/theorems/0f0fbf26-9730-5a1c-b0cc-210acb35dea9
-- title:
--   (6) — conditional on $D_1$, the coverage $P(\xi\in U)=F(t(\xi^2_{(i^*)}))$ is distributed as $U_{(i^*)}\sim\mathrm{Beta}(i^*,n_2-i^*+1)$
-- statement:
--   Let $P$ be a probability measure on a measurable space $E$, $0<\epsilon<1$, $0<\delta<1$ and $n_2\ge\log\delta/\log(1-\epsilon)$, so that the index $i^*$ of (4) is a valid rank. Fix a realization $d_1$ of the Phase 1 data $D_1$, and let $t=t(d_1,\cdot):E\to\mathbb R$ be the score map built from it, measurable and such that $t(\xi)$, $\xi\sim P$, has an atomless law with distribution function $F$. Let $D_2=(\xi^2_1,\dots,\xi^2_{n_2})$ be i.i.d. from $P$ and $U=\{\xi: t(\xi)\le t(\xi^2_{(i^*)})\}$. Then:
--
--   1. the coverage $D_2\mapsto P(\xi\in U)$ is measurable;
--   2. for every realization of $D_2$,
--   $$P(\xi\in U)=P\big(t(\xi)\le t(\xi^2_{(i^*)})\big)=F\big(t(\xi^2_{(i^*)})\big);$$
--   3. conditional on $D_1=d_1$, $P(\xi\in U)\overset{d}{=}U_{(i^*)}$, the $i^*$-th ranked variable among $n_2$ i.i.d. uniform variables on $[0,1]$;
--   4. $U_{(i^*)}$ has the $\mathrm{Beta}(i^*,n_2-i^*+1)$ distribution.
--
--   So the tolerance level actually achieved by the learned set is a Beta random variable; Theorem 2 studies its concentration as $n_2\to\infty$.
--
--   **Formalization Note** Conditioning on $D_1$ is the section at $d_1$, with $D_2\sim P^{n_2}$. $F$ is Mathlib's `cdf` of the law of $t(\xi)$; the Beta law is Mathlib's `betaMeasure`. The coverage is used as a real number.
--
--   Differences from the source:
--   - reading: ϵ, δ levels (range not stated in the theorem) → 0 < ϵ < 1, 0 < δ < 1; reason: the paper's standing range (p.1, p.5); log(1 − ϵ) and the quantiles need it
--   - reading: t(ξ), ξ ~ P, is a continuous random variable → the law of t(d₁, ξ), ξ ~ P, is atomless (NullSingletonClass) at the fixed realization d₁, and t(d₁, ·) is measurable; reason: the weakest standard meaning, as in the published (5); atomlessness of P follows and is not assumed separately
--   - generalization: ξ ∈ ℝᵐ, P a continuous distribution, t a map constructed from D₁, assumptions for every D₁ → any measurable space E, any probability measure P, hypotheses only at the fixed realization d₁; reason: the statement is conditional on D₁ = d₁; under Theorem 1's assumptions every d₁ satisfies the hypotheses, so it specializes to the paper's setting
--   - encoding: conditional on D₁ → the section at a fixed realization d₁, D₂ ~ P^{n₂} (Measure.pi); reason: D₂ is independent of D₁, so the conditional law of D₂ is P^{n₂}; same encoding as the published (5)
--   - encoding: P(ξ ∈ U) =d U₍ᵢ*₎, or equivalently Beta(i*, n₂ − i* + 1) → the push-forward of P^{n₂} under d₂ ↦ P(U(d₁, d₂)) (as a real number) equals the law of U₍ᵢ*₎, which equals Mathlib's betaMeasure i* (n₂ − i* + 1); measurability of d₂ ↦ P(U(d₁, d₂)) is stated as a conclusion; reason: equality in distribution is equality of laws; measurability makes the push-forward meaningful
--   - encoding: the sample-size condition of Theorem 1 (implicit in 'U' with i* of (4)) → hypothesis n₂ ≥ log δ / log(1 − ϵ); reason: it makes i* a valid rank (published iStar_valid_iff); i* is undefined otherwise
--   - encoding: ranked observations t(ξ²₍₁₎) < ⋯ < t(ξ²₍ₙ₂₎) and U₍ᵢ*₎ → order statistics with multiplicity (base orderStat); reason: ties have probability zero under the atomless hypothesis
-- source:
--   Hong–Huang–Lam, arXiv:1704.04342v2, (6) and the sentence after it, p.10

import Mathlib
import Definitions.Def_LearningBasedRO_Model
import Definitions.Def_LearningBasedRO_Supplement_uniformOrderStatLaw

open MeasureTheory ProbabilityTheory

namespace LearningBasedRO.Supplement

/-- **(6).** Conditional on `D₁ = d₁`, the coverage of the learned set is
`P(ξ ∈ U) = P(t(ξ) ≤ t(ξ²₍ᵢ*₎)) = F(t(ξ²₍ᵢ*₎))`, with `F` the distribution function of `t(ξ)`,
`ξ ~ P`, and it is distributed as `U₍ᵢ*₎`, the `i*`-th ranked variable among `n₂` uniform variables
on `[0,1]`, equivalently as `Beta(i*, n₂ - i* + 1)`.
Hong–Huang–Lam, arXiv:1704.04342v2, (6) and the sentence after it, p.10.

**Formalization Note** "Conditional on `D₁`" is the section at a fixed realization `d₁`: the law is
over `D₂ ~ P^{n₂}` (`Measure.pi`). The hypotheses are those of Theorem 1 at `d₁` (`t d₁`
measurable, `t(ξ)` atomless, i.e. "continuous"), with the sample-size condition that makes `i*`
a valid rank. Conclusions: the coverage `d₂ ↦ P(U(d₁, d₂))` (as a real number) is measurable, it
equals `F(t(ξ²₍ᵢ*₎))` pointwise (`F = cdf (P ∘ (t d₁)⁻¹)`), its law is that of `U₍ᵢ*₎`, and the
law of `U₍ᵢ*₎` is Mathlib's `betaMeasure i* (n₂ - i* + 1)`. Order statistics keep ties. -/
theorem display_6 {E : Type*} [MeasurableSpace E] (P : Measure E) [IsProbabilityMeasure P]
    (n₁ n₂ : ℕ) (ϵ δ : ℝ) (hϵ0 : 0 < ϵ) (hϵ1 : ϵ < 1) (hδ0 : 0 < δ) (hδ1 : δ < 1)
    (hn₂ : Real.log δ / Real.log (1 - ϵ) ≤ (n₂ : ℝ)) (t : (Fin n₁ → E) → E → ℝ)
    (d₁ : Fin n₁ → E) (ht : Measurable (t d₁)) (hcont : NullSingletonClass (P.map (t d₁))) :
    Measurable (fun d₂ : Fin n₂ → E => (P (uncertaintySet t ϵ δ (d₁, d₂))).toReal) ∧
      (∀ d₂ : Fin n₂ → E, (P (uncertaintySet t ϵ δ (d₁, d₂))).toReal =
        cdf (P.map (t d₁)) (orderStat (fun i => t d₁ (d₂ i)) (iStar n₂ ϵ δ))) ∧
      (Measure.pi fun _ : Fin n₂ => P).map
          (fun d₂ : Fin n₂ → E => (P (uncertaintySet t ϵ δ (d₁, d₂))).toReal) =
        uniformOrderStatLaw n₂ (iStar n₂ ϵ δ) ∧
      uniformOrderStatLaw n₂ (iStar n₂ ϵ δ) =
        betaMeasure (iStar n₂ ϵ δ : ℝ) ((n₂ : ℝ) - (iStar n₂ ϵ δ : ℝ) + 1) := by sorry

end LearningBasedRO.Supplement
