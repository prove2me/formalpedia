-- Prove2me | Theorems.Thm_KingRockAsymp_Distribution_theorem_2_6
-- name    : KingRockAsymp.Distribution.theorem_2_6
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T13:06:31.742979+00:00
-- url     : https://prove2.me/theorems/c9223209-c2df-4440-b75f-3232645bf8fd
-- title:
--   Theorem 2.6 — asymptotic distributions of solutions of a generalized equation with random data
-- statement:
--   Let $Z$ be a separable Banach space with its Borel $\sigma$-algebra, and assume the analytical assumptions M.1–M.4 at $(z^*,x^*)$ for $f : Z \times \mathbb R^n \to \mathbb R^m$ and $N : \mathbb R^n \rightrightarrows \mathbb R^m$, with strong partial B-derivative $D_z f(z^*,x^*)$; let $F = f(z^*,\cdot) + N$. Let $\tau_\nu > 0$ be numbers with $\tau_\nu \to 0$, and let $z^\nu$ be random variables in $Z$ on a probability space $(\Omega,P)$ such that
--   $$\tau_\nu^{-1}\big[z^\nu - z^*\big] \xrightarrow{\ \mathcal D\ } w$$
--   for a random variable $w$ in $Z$ (on its own probability space). Let $x^\nu$ be measurable maps such that, for every $\nu$, $x^\nu$ is almost surely a solution of $0 \in f(z^\nu, x) + N(x)$, and suppose $x^\nu \to x^*$ almost surely. Then there is a map $L : Z \to \mathbb R^n$ with $L(w) \in DF^{-1}(0|x^*)\big(-D_z f(z^*,x^*)(w)\big)$ for every $w \in Z$ — that is, $L(w)$ is the unique element of that set, by M.4 — such that
--   $$\tau_\nu^{-1}\big[x^\nu - x^*\big] \xrightarrow{\ \mathcal D\ } L(w) = DF^{-1}(0|x^*)\big(-D_z f(z^*,x^*)(w)\big).$$
--
--   This is the paper's abstract limit theorem: the asymptotic law of the solutions is the image of the asymptotic law of the data under the contingent derivative of $F^{-1}$, a positively homogeneous but in general nonlinear map, so the limit need not be normal even when $w$ is.
--
--   **Formalization Note** The paper states: "if a sequence $\{x^\nu\}$ of measurable selections … converges almost surely, it converges to the point $x^*$". This fails when $J(z^*)$ has another point: with $n = m = 1$, $Z = \mathbb R$, $N \equiv \{0\}$, $f(z,x) = x^2 - x - z$, $z^* = x^* = 0$, assumptions M.1–M.4 hold, $J(0) = \{0,1\}$, and solutions near $1$ converge almost surely to $1$. We therefore assume that the almost sure limit is $x^*$, and drop that clause from the conclusion. "$\{\tau_\nu\}$ tends to $0$" is from p. 7. Convergence in distribution is Mathlib's `TendstoInDistribution` (weak convergence of laws), with the limit on a separate probability space. The selection property is required almost surely for every $\nu$.
-- source:
--   King & Rockafellar, Asymptotic Theory for Solutions in Statistical Estimation and Stochastic Programming, Math. Oper. Res. 18(1) (1993), Theorem 2.6, p. 8 (authors' manuscript pagination)

import Mathlib
import Definitions.Def_KingRockAsymp_Distribution_Basic

namespace KingRockAsymp.Distribution

open Set Filter Topology Metric MeasureTheory ProbabilityTheory

theorem theorem_2_6 {Z : Type*} [NormedAddCommGroup Z] [NormedSpace ℝ Z] [CompleteSpace Z]
    [TopologicalSpace.SeparableSpace Z] [MeasurableSpace Z] [BorelSpace Z] {n m : ℕ}
    {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    (P : Measure Ω) [IsProbabilityMeasure P] (μ' : Measure Ω') [IsProbabilityMeasure μ']
    (f : Z → Rn n → Rn m) (N : Rn n → Set (Rn m)) (z₀ : Z) (x₀ : Rn n) (Dz : Z → Rn m)
    (hM : AnalyticalAssumptions f N z₀ x₀ Dz)
    (τ : ℕ → ℝ) (hτpos : ∀ ν, 0 < τ ν) (hτ : Tendsto τ atTop (𝓝 0))
    (z : ℕ → Ω → Z) (hz : ∀ ν, Measurable (z ν))
    (W : Ω' → Z) (hW : Measurable W)
    (hconv : TendstoInDistribution (fun ν ω => (τ ν)⁻¹ • (z ν ω - z₀)) atTop W
      (fun _ => P) μ')
    (x : ℕ → Ω → Rn n) (hx : ∀ ν, Measurable (x ν))
    (hsel : ∀ ν, ∀ᵐ ω ∂P, x ν ω ∈ solMap f N (z ν ω))
    (hlim : ∀ᵐ ω ∂P, Tendsto (fun ν => x ν ω) atTop (𝓝 x₀)) :
    ∃ L : Z → Rn n,
      (∀ w : Z, L w ∈ contingentDeriv (svInv (fPlusN f N z₀)) 0 x₀ (-(Dz w))) ∧
      TendstoInDistribution (fun ν ω => (τ ν)⁻¹ • (x ν ω - x₀)) atTop
        (fun ω' => L (W ω')) (fun _ => P) μ' := by sorry

end KingRockAsymp.Distribution
