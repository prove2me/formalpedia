-- Prove2me | Theorems.Thm_OnlineConvexOpt_BanditConvex_fkm_algorithm_regret_v2
-- name    : OnlineConvexOpt.BanditConvex.fkm_algorithm_regret_v2
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-10-06T06:21:34.085164+00:00
-- url     : https://prove2.me/theorems/3898271a-a125-441b-b66e-533fa7b88c40
-- title:
--   Theorem 6.9 — FKM bandit regret $9nDGT^{3/4}$ (corrected comparator, shrunk set, independence; $G\ge1$)
-- statement:
--   **Statement (Theorem 6.9).** Let $K\subseteq\mathbb R^n$ ($n\ge1$) be a closed convex set containing the unit ball centered at $0$, of diameter at most $D$, and let $f_0,f_1,\dots$ be cost functions that are convex and $G$-Lipschitz on $K$ ($G\ge1$) and bounded by $1$ in absolute value on $K$. Run the FKM algorithm (Algorithm 23) with $\eta=D/(nT^{3/4})$ and $\delta=T^{-1/4}$ on the shrunk set $K_\delta=(1-\delta)K$: $x_0=0$, independent uniform unit vectors $u_t\sim S$, $y_t=x_t+\delta u_t$ played, $g_t=\frac n\delta f_t(y_t)u_t$, $x_{t+1}=\Pi_{K_\delta}[x_t-\eta g_t]$. Then for every $T\ge1$,
--   $$\sum_{t=1}^{T}\mathbb E[f_t(y_t)]-\min_{x\in K}\sum_{t=1}^{T}f_t(x)\;\le\;9nDG\,T^{3/4}=O(T^{3/4}).$$
--
--   **Formalization Note.** Four corrections. (i) The comparator is the real infimum of $\{\sum_t f_t(z):z\in K\}$ (genuine: $K$ nonempty, costs bounded on $K$), replacing the junk-valued binder `⨅ z ∈ K` of the retired version. (ii) $K_\delta$ is defined as the dilate $(1-\delta)\cdot K$ (Mathlib's pointwise scalar multiple of a set) instead of $\{z:(1-\delta)^{-1}z\in K\}$, which at $T=1$ ($\delta=1$) collapsed to the whole space through $0^{-1}=0$. (iii) Standing assumptions of the BCO setting dropped by the retired version are restored: the costs are convex on $K$ (Lemma 6.5 needs the full-information regret bound of OGD, which holds for convex costs), $K$ is closed, the sphere samples $u_t$ are mutually independent (`iIndepFun`; Lemma 6.7's unbiasedness $\mathbb E[g_t\mid x_t]=\nabla\hat f_t(x_t)$ needs $u_t$ independent of the past), and `IsUniformOnUnitSphere` (now from `OnlineConvexOpt_BanditConvex_UniformOnUnitSphere_v2`) requires $u_t$ measurable, without which Mathlib's `Measure.map` is the zero measure and the rotation-invariance clause pins down no law. (iv) The hypothesis $G\ge1$ is added: the book's own derivation ends with $\eta n^2T/\delta^2+D^2/\eta+4\delta DGT=(n+4G)DT^{3/4}$ (the first two terms carry no $G$, as $\|g_t\|\le n/\delta$ uses only $|f_t|\le1$), which is $\le9nDGT^{3/4}$ only when $G\ge1$; for $G<1$ the printed bound is false (the iterates barely move while the regret is $\approx TG$), and since any $G$-Lipschitz cost is $\max(G,1)$-Lipschitz the restriction loses nothing in substance. Integrability of $f_t(y_t)$ remains an explicit hypothesis. Rounds are $0$-indexed.
-- source:
--   Hazan, Introduction to Online Convex Optimization, 2nd ed., arXiv:1909.05207v3, p. 113, Theorem 6.9 (PDF p. 135) — with the normalization G ≥ 1 that the printed constant 9nDG requires

import Mathlib
import Definitions.Def_OnlineConvexOpt_BanditConvex_UniformOnUnitSphere_v2
import Definitions.Def_OnlineConvexOpt_FirstOrder_Protocol_v2

open MeasureTheory
open scoped Pointwise

namespace OnlineConvexOpt.BanditConvex

/-- Theorem 6.9 (Hazan, *Introduction to Online Convex Optimization*, 2nd ed.,
arXiv:1909.05207v3, p. 113, PDF p. 135). Algorithm 23 (the FKM algorithm) with parameters
`η = D / (n T^{3/4})`, `δ = 1 / T^{1/4}` guarantees the following expected regret bound:
`Σ_{t=1}^T E[f_t(y_t)] - min_{x ∈ K} Σ_{t=1}^T f_t(x) ≤ 9 n D G T^{3/4} = O(T^{3/4})`.

`K ⊆ EuclideanSpace ℝ (Fin n)` is a closed convex set containing the unit ball centered at `0`
(p. 112, PDF p. 134), of diameter `≤ D`, and carries convex, `G`-Lipschitz cost functions `f_t`
bounded by `1` in absolute value on `K` (the chapter's standing assumptions for Algorithm 23,
stated as explicit hypotheses). `Kδ = (1 - δ)K` is the shrunk Minkowski set (p. 112) that
Algorithm 23 projects onto. `u_t ∼ S` are independent uniformly drawn unit vectors (fresh draws
at every round, independent of the past), `y_t = x_t + δ u_t` the played point, and
`g_t = (n/δ) f_t(y_t) u_t` the gradient estimate driving the projected-gradient update
`x_{t+1} = Π_{Kδ}[x_t - η g_t]` of line 5 of Algorithm 23.

Corrected version. (i) The comparator is the genuine infimum of the cumulative cost over `K`
(the retired `⨅ z ∈ K` binder returned the junk value `0` outside `K`); it is the book's `min`
since the costs are bounded on the nonempty `K`. (ii) `Kδ` is defined as the dilate `(1-δ) • K`
instead of `{z | (1-δ)⁻¹ z ∈ K}`, which at `T = 1` (`δ = 1`) collapsed to the whole space through
Lean's `0⁻¹ = 0`. (iii) The standing assumptions dropped by the retired version are restored:
the costs are convex on `K` (the BCO setting; Lemma 6.5 needs the full-information regret bound
of OGD, which holds for convex costs only), `K` is closed, and the sphere samples `u_t` are
mutually independent (Algorithm 23 draws a fresh `u_t` each round; the unbiasedness
`E[g_t | x_t] = ∇f̂_t(x_t)` of Lemma 6.7 needs `u_t` independent of the past). (iv) The
hypothesis `1 ≤ G` is added: the book's final step absorbs the `η n² T/δ² + D²/η = n D T^{3/4}`
terms of its own derivation — which carry no factor `G` — into `9nDGT^{3/4}`, which is only
valid for `G ≥ 1` (for `G < 1` the printed bound fails; any `G`-Lipschitz cost is also
`max(G,1)`-Lipschitz, so the restriction loses no generality in substance). -/
theorem fkm_algorithm_regret_v2
    {n : ℕ} (hn : 0 < n)
    {Ω : Type*} [MeasurableSpace Ω] {Prob : Measure Ω} [IsProbabilityMeasure Prob]
    (K Kδ : Set (EuclideanSpace ℝ (Fin n))) (hKconv : Convex ℝ K) (hKclosed : IsClosed K)
    (hKball : Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) 1 ⊆ K)
    (D G : ℝ) (hDpos : 0 < D) (hG1 : 1 ≤ G)
    (hD : ∀ x ∈ K, ∀ y ∈ K, dist x y ≤ D)
    (T : ℕ) (hT : 1 ≤ T)
    (η δ : ℝ) (hη : η = D / ((n : ℝ) * (T : ℝ) ^ (3 / 4 : ℝ)))
    (hδ : δ = 1 / (T : ℝ) ^ (1 / 4 : ℝ))
    (hKδ : Kδ = (1 - δ) • K)
    (f : ℕ → EuclideanSpace ℝ (Fin n) → ℝ)
    (hfconv : ∀ t, ConvexOn ℝ K (f t))
    (hfG : ∀ t, ∀ x ∈ K, ∀ y ∈ K, |f t x - f t y| ≤ G * dist x y)
    (hfbdd : ∀ t, ∀ x ∈ K, |f t x| ≤ 1)
    (x y u g : ℕ → Ω → EuclideanSpace ℝ (Fin n))
    (hx0 : ∀ ω, x 0 ω = 0)
    (hu : ∀ t, IsUniformOnUnitSphere Prob (u t))
    (huind : ProbabilityTheory.iIndepFun u Prob)
    (hy : ∀ t ω, y t ω = x t ω + δ • u t ω)
    (hg : ∀ t ω, g t ω = ((n : ℝ) / δ * f t (y t ω)) • u t ω)
    (hstep : ∀ t ω,
      OnlineConvexOpt.FirstOrder.IsMetricProjection Kδ (x t ω - η • g t ω) (x (t + 1) ω))
    (hint : ∀ t, Integrable (fun ω => f t (y t ω)) Prob) :
    (∑ t ∈ Finset.range T, ∫ ω, f t (y t ω) ∂Prob) -
        sInf ((fun z => ∑ t ∈ Finset.range T, f t z) '' K) ≤
      9 * n * D * G * (T : ℝ) ^ (3 / 4 : ℝ) := by sorry

end OnlineConvexOpt.BanditConvex
