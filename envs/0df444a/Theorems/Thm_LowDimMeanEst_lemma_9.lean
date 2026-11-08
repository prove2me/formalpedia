-- Prove2me | Theorems.Thm_LowDimMeanEst_lemma_9
-- name    : LowDimMeanEst.lemma_9
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T04:55:07.711992+00:00
-- url     : https://prove2.me/theorems/d7a4897d-e5d8-465b-8b9c-6a2373b0d182
-- title:
--   Lemma 9 — Chernoff bound for a fixed large-trace $A\succeq0$ and unit $z$: $P[F\ge-(1+4|a|)\log\frac1\delta/\log\log\frac1\delta]\le\delta/(100d\log\frac1\delta)^{5d^2}$
-- statement:
--   **Lemma 9.** There is $\xi_0>0$ such that for every $\xi\in(0,\xi_0)$ there are constants $C_\xi,B_\xi>0$ with the following property. Let $d,n\ge1$, $\delta\in(0,\frac13]$, $\gamma\ge0$, and let $D$ be a distribution on $\mathbb R^d$ with mean $\mu$ and $\mathbb E[XX^\top]\preceq(1+\gamma)I$; let $x_1,\dots,x_n$ be i.i.d. from $D$. Put $L=\log\frac1\delta$, $LL=\log\log\frac1\delta$ and
--
--   $$\eta=C_\xi\Big(\sqrt{\gamma+\tfrac dL}+\tfrac1{LL}+\tfrac{d^2(\log d+LL)}{L}\sqrt{1+\gamma+\tfrac dL}\Big).$$
--
--   For every $A\succeq0$ with $\mathrm{Tr}(A)\ge\xi\,\dfrac{L/n}{1+d/L}$ there are $a\in\mathbb R$, $b\ge0$, $t>0$ with $|a|,|b|,\sqrt{\frac{1+d/L}{nL}}\,|t|\le B_\xi$ such that for every unit vector $z$,
--
--   $$\Pr\Big[F(x,A,z,a,b,t)\ \ge\ -\frac{(1+4|a|)L}{LL}\Big]\ \le\ \frac{\delta}{(100\,d\,L)^{5d^2}}, \tag{12}$$
--
--   where $F$ is Definition 10 (the left-hand side of (12)) with this $\eta$ and $\mu$.
--
--   For a fixed matrix and direction this says: with overwhelming probability, either $A$ is not the trimming matrix of the samples or the trimmed mean errs by little in direction $z$. The net arguments of §8 lift it to all small-trace matrices and all directions.
--
--   **Formalization Note** $O_\xi(\cdot)$ is the constant $C_\xi$, chosen after $\xi$ and before all other data; the parameters $a,b,t$ depend on $A$ (and $d,n,\delta,\gamma,D$) but not on $z$. The same parameters satisfy (12) and the "Furthermore" bounds.
--
--   Differences from the source:
--   - encoding: "for any sufficiently small universal constant ξ"; η = O_ξ(·) → ∃ ξ₀ > 0, ∀ ξ ∈ (0, ξ₀), ∃ C_ξ, B_ξ > 0 before d, n, δ, γ, D, A; reason: the quantifier order the statement prescribes
--   - reading: "it is possible to choose the parameters such that |a|, |b|, √((1 + d/L)/(nL))|t| are bounded" → the same a, b, t satisfy (12) and the bounds; reason: the stronger of the two readings; the proof chooses one set of parameters (p.23)
--   - encoding: d, n implicit → 1 ≤ d and 1 ≤ n; reason: standing assumptions: d ≥ 1 (p.13, Lemma 25) and n samples; only excludes degenerate cases
--   - encoding: δ ≤ 1/3 → 0 < δ ≤ 1/3; reason: δ is a probability parameter
-- source:
--   Lee, Mathashery, Valiant, Wang, Optimal Sub-Gaussian Mean Estimation in Low Dimensions, STOC 2027 submission (manuscript sha256 7316d30e…), Lemma 9, p.16 (proof pp.22–23)

import Mathlib
import Definitions.Def_LowDimMeanEst_ChernoffF
import Definitions.Def_LowDimMeanEst_Parameters

open MeasureTheory

namespace LowDimMeanEst

/-- **Lemma 9**, p.16 (proof pp.22–23).

Lee, Mathashery, Valiant, Wang, *Optimal Sub-Gaussian Mean Estimation in Low Dimensions*, STOC 2027
submission (manuscript sha256 7316d30e…).

"For any sufficiently small universal constant ξ ≪ 1, the following holds. Suppose the failure
probability δ ≤ 1/3. Consider a distribution D on ℝᵈ with mean µ and second moment matrix
E[XX⊤] ⪯ (1 + γ)I for some γ ≥ 0. Let x₁, …, xₙ denote n i.i.d. samples drawn from D. Define
η = O_ξ(√(γ + d/log(1/δ)) + 1/log log(1/δ) + (d²(log d + log log(1/δ))/log(1/δ))
√(1 + γ + d/log(1/δ))). Now consider an arbitrary A ⪰ 0 such that
Tr(A) ≥ ξ · (log(1/δ)/n)/(1 + d/log(1/δ)). There exist parameters a ∈ ℝ, b ≥ 0, and t > 0 such that
for any unit vector z,
P[ a(Σᵢ min(1, xᵢ⊤Axᵢ) − (1/3) log(1/δ)) + b(Σᵢ (1 − min(1, xᵢ⊤Axᵢ))xᵢ⊤Axᵢ − Tr(A) Σᵢ (1 − min(1,
xᵢ⊤Axᵢ))(xᵢ · z)²) + t((1/n) Σᵢ (1 − min(1, xᵢ⊤Axᵢ))(xᵢ · z) − ((1 + η)√(2 log(1/δ)/n) + µ · z))
≥ −(1 + 4|a|) log(1/δ)/log log(1/δ) ] ≤ δ/(100d log(1/δ))^{5d²} (12)
Furthermore, it is possible to choose the parameters such that |a|, |b|,
√((1 + d/log(1/δ))/(n log(1/δ))) |t| are all upper bounded by a function of the assumed small
universal constant ξ."

**Formalization Note.**
* "Sufficiently small universal constant ξ" is `∀ ξ ∈ (0, ξ0)` for a universal `ξ0 > 0`. For each
  such `ξ` there are `Cξ` (the constant of `O_ξ` in `η`, `η = etaFixed Cξ d γ δ`) and `Bξ` (the bound
  on the parameters), chosen before `d, n, δ, γ, D, A`.
* The parameters `a, b, t` depend on `A` (and on `d, n, δ, γ, D`) and are chosen before `z`.
* The left-hand side of (12) is `chernoffF` (Definition 10) with `µ = E[X]`.
* `d ≥ 1` and `n ≥ 1` are the paper's standing assumptions (`d ≥ 1`, p.13; `n` samples).
-/
theorem lemma_9 :
    ∃ ξ0 : ℝ, 0 < ξ0 ∧ ∀ ξ : ℝ, 0 < ξ → ξ < ξ0 →
      ∃ Cξ Bξ : ℝ, 0 < Cξ ∧ 0 < Bξ ∧
        ∀ (d n : ℕ) (δ γ : ℝ), 1 ≤ d → 1 ≤ n → 0 < δ → δ ≤ 1 / 3 → 0 ≤ γ →
          ∀ (D : Measure (E d)) [IsProbabilityMeasure D], SecondMomentLe D (1 + γ) →
            ∀ A : E d →L[ℝ] E d, A.IsPositive →
              ξ * logInv δ / (n * (1 + d / logInv δ)) ≤ tr A →
              ∃ a b t : ℝ, 0 ≤ b ∧ 0 < t ∧ |a| ≤ Bξ ∧ |b| ≤ Bξ ∧
                Real.sqrt ((1 + d / logInv δ) / (n * logInv δ)) * |t| ≤ Bξ ∧
                ∀ z : E d, ‖z‖ = 1 →
                  (Measure.pi fun _ : Fin n => D)
                      {x | -(1 + 4 * |a|) * logInv δ / loglogInv δ ≤
                        chernoffF δ (etaFixed Cξ d γ δ) (popMean D) x A z a b t} ≤
                    ENNReal.ofReal (δ / (100 * d * logInv δ) ^ (5 * d ^ 2)) := by sorry

end LowDimMeanEst
