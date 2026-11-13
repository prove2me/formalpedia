-- Prove2me | Theorems.Thm_HDXHitting_fact_2_1_bipartite
-- name    : HDXHitting.fact_2_1_bipartite
-- status  : Proved
-- author  : @iris
-- created : 2026-11-08T17:57:30.173077+00:00
-- url     : https://prove2.me/theorems/e1d251ea-f946-4fc4-b0a2-d6891566ccb0
-- title:
--   Fact 2.1 (bipartite form) — $|\mathbb E[f(u)g(v)]-\mu\nu|\le\lambda\sqrt{\mu(1-\mu)\nu(1-\nu)}\le\lambda\sqrt{\mu\nu}$
-- statement:
--   Let $G=(U,W,E)$ be a bipartite graph with nonnegative edge weights $B$ of total mass $1$, stationary measures $\pi_U(u)=\sum_w B(u,w)$ and $\pi_W(w)=\sum_u B(u,w)$, whose random-walk operator from $L^2(\pi_W)$ to $L^2(\pi_U)$ has second largest singular value at most $\lambda\ge0$. Then for $f:U\to[0,1]$ and $g:W\to[0,1]$ with means $\mu=\mathbb E_{\pi_U}f$ and $\nu=\mathbb E_{\pi_W}g$,
--   $$
--   \big|\mathbb E_{(u,w)\sim E}[f(u)g(w)]-\mu\nu\big|\le\lambda\sqrt{\mu(1-\mu)\nu(1-\nu)}\le\lambda\sqrt{\mu\nu},
--   $$
--   where the edge is drawn with probability $B(u,w)$.
--
--   This bipartite mixing bound is applied to colour pairs in the proof of the partite bound (3).
--
--   Differences from the source:
--   - encoding: a bipartite graph G = (U, V, E) and its second singular value → finite types U, W, nonnegative weights B of total mass 1, and BipSingLE B lam; reason: weighted edge distribution; the singular value as the walk's norm on mean-zero functions
-- source:
--   Bafna–Tjowasi, A Hitting Set Lemma for HDX & Applications, STOC 2027 submission (manuscript sha256 60d23b0d…), Fact 2.1 (bipartite form), p.11

import Mathlib
import Definitions.Def_HDXHitting_BipSingLE

namespace HDXHitting

/-- Fact 2.1, bipartite form (Bafna–Tjowasi, *A Hitting Set Lemma for HDX & Applications*, STOC 2027 submission manuscript (sha256 60d23b0d…e56d3), p.11): let `G = (U, W, E)` be a bipartite graph with
nonnegative edge weights `B` of total mass `1` whose random-walk operator from `L²(π_W)` to
`L²(π_U)` has second largest singular value at most `λ ≥ 0`, where `π_U(u) = ∑_w B(u, w)` and
`π_W(w) = ∑_u B(u, w)`. Then for `f : U → [0, 1]`, `g : W → [0, 1]` with means `µ = E_{π_U} f`,
`ν = E_{π_W} g`,
`|E_{(u,w)∼E}[f(u) g(w)] − µν| ≤ λ √(µ(1 − µ)ν(1 − ν)) ≤ λ √(µν)`. -/
theorem fact_2_1_bipartite {U W : Type*} [Fintype U] [Fintype W] (B : U → W → ℝ)
    (hB0 : ∀ u w, 0 ≤ B u w) (hB1 : ∑ u, ∑ w, B u w = 1) (lam : ℝ) (hlam : 0 ≤ lam)
    (hB : BipSingLE B lam) (f : U → ℝ) (g : W → ℝ) (hf : ∀ u, 0 ≤ f u ∧ f u ≤ 1)
    (hg : ∀ w, 0 ≤ g w ∧ g w ≤ 1) (μ ν : ℝ) (hμ : μ = ∑ u, (∑ w, B u w) * f u)
    (hν : ν = ∑ w, (∑ u, B u w) * g w) :
    |∑ u, ∑ w, B u w * f u * g w - μ * ν| ≤ lam * Real.sqrt (μ * (1 - μ) * ν * (1 - ν)) ∧
      lam * Real.sqrt (μ * (1 - μ) * ν * (1 - ν)) ≤ lam * Real.sqrt (μ * ν) := by sorry

end HDXHitting
