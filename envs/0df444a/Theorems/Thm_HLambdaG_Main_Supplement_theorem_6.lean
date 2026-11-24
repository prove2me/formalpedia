-- Prove2me | Theorems.Thm_HLambdaG_Main_Supplement_theorem_6
-- name    : HLambdaG.Main.Supplement.theorem_6
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-24T01:05:57.242798+00:00
-- url     : https://prove2.me/theorems/ac3aaabd-f213-4e77-80bf-be533061fb46
-- title:
--   Theorem 6, p. 642 — continuous L = λW: under s⁻¹T₁(s) → λ⁻¹ and s⁻¹w(s) → 0, G → W iff H → L, and then L = λW
-- statement:
--   Consider the continuous $L=\lambda W$ setting (§1.6 with (13) and (25)). Customer $u\ge0$ arrives at $T_1(u)$, where $T_1$ is a nonnegative, finite, nondecreasing, right-continuous function with $T_1(s)\to\infty$. It waits $w(u)$, where $w\ge0$ is right-continuous and integrable on every bounded interval $[0,s]$. With $F_u(t)=\min\{w(u),(t-T_1(u))^+\}$, the averages (12) are
--   $$
--   G(s)=s^{-1}\int_0^sw(u)\,du,\qquad H(t)=t^{-1}\int_0^\infty F_u(t)\,du .
--   $$
--   Suppose that, for some $0<\lambda<\infty$,
--   $$
--   s^{-1}T_1(s)\to\lambda^{-1}\quad\text{and}\quad s^{-1}w(s)\to0\qquad(s\to\infty).
--   $$
--   Then $G(s)$ converges to a finite limit $W$ if and only if $H(t)$ converges to a finite limit $L$, in which case
--   $$
--   L=\lambda W .
--   $$
--
--   This is the continuous analogue of $L=\lambda W$ in Rolski and Stidham's setting. The growth condition $s^{-1}w(s)\to0$ replaces their condition (III).
--
--   **Formalization Note** The page writes $\lim_{n\to\infty}G(n)$. Here $G$ is the average (12) along real $s\to\infty$. For $w\ge0$ the two limits agree, because $\frac{n}{s}G(n)\le G(s)\le\frac{n+1}{s}G(n+1)$ for $n\le s<n+1$. Condition (13) calls $f$ "integrable on $[0,\infty)\times[0,\infty)$". Read globally, this would force $\int_0^\infty w<\infty$ and $W=0$. The Lean statement generalizes this to integrability of $w$ on every $[0,s]$: $F_u$ is then integrable in $u$ for each $t$, as (12) requires, and $G$, $H$ are never Lean's junk value of a non-integrable integral. $F_u(t)$ is the closed form of $\int_0^t1_{[T_1(u),T_1(u)+w(u)]}(v)\,dv$ for $w(u)\ge0$. $w$ is a function on $\mathbb R_{\ge0}$; right continuity is continuity within $[u,\infty)$ at each $u$.
--
--   Differences from the source:
--
--   - encoding: lim_{n→∞} G(n) = W → Tendsto (contG w) atTop (𝓝 W) along real s; reason: for w ≥ 0, (n/s)G(n) ≤ G(s) ≤ ((n+1)/s)G(n+1) on [n, n+1), so the integer and real limits exist together and coincide; G of (12) is defined for real s
--   - generalization: (13): f integrable on the whole nonnegative quadrant → w integrable on each bounded interval [0,s]; reason: global integrability of the nonnegative indicator (25) implies local integrability of w by Tonelli, so every printed instance is included. The enlarged domain also permits positive limiting W; truncating any fixed initial interval and using w(u) ≤ εu in the tail supports the same conclusion without global integrability
--   - encoding: F_u(t) = ∫₀ᵗ 1_[T₁(u), T₁(u)+w(u)](v) dv → contF: min (w u) (max 0 (t − T₁ u)); reason: equal for w(u) ≥ 0, which is a hypothesis
-- source:
--   Glynn and Whitt, Extensions of the queueing relations L = λW and H = λG, Oper. Res. 37 (1989), p. 642, Theorem 6, with (12) p. 637, (13) p. 638 and (25) p. 642; https://doi.org/10.1287/opre.37.4.634

import Mathlib
import Definitions.Def_HLambdaG_Main_Supplement_Continuous

open scoped NNReal

namespace HLambdaG.Main.Supplement

open Filter Topology MeasureTheory

/-- Theorem 6, p. 642: in the continuous `L = λW` setting ((13) with (25)), if
`s⁻¹T₁(s) → λ⁻¹` and `s⁻¹w(s) → 0`, then `G(s) → W` for some finite `W` iff `H(t) → L` for
some finite `L`, in which case `L = λW`. -/
theorem theorem_6 (τ₁ : TimeChange) (w : ℝ≥0 → ℝ) (lam : ℝ) (hlam : 0 < lam)
    (hw_nonneg : ∀ u, 0 ≤ w u)
    (hw_rcont : ∀ u, ContinuousWithinAt w (Set.Ici u) u)
    (hw_int : ∀ s : ℝ, IntegrableOn (fun u : ℝ => w u.toNNReal) (Set.Icc 0 s))
    (hT₁ : Tendsto (fun s : ℝ≥0 => (τ₁.T s : ℝ) / (s : ℝ)) atTop (𝓝 lam⁻¹))
    (hw : Tendsto (fun s : ℝ≥0 => w s / (s : ℝ)) atTop (𝓝 0)) :
    ((∃ W : ℝ, Tendsto (contG w) atTop (𝓝 W)) ↔
      (∃ L : ℝ, Tendsto (contH τ₁ w) atTop (𝓝 L))) ∧
      ∀ W L : ℝ, Tendsto (contG w) atTop (𝓝 W) →
        Tendsto (contH τ₁ w) atTop (𝓝 L) → L = lam * W := by sorry

end HLambdaG.Main.Supplement
