-- Prove2me | Theorems.Thm_HDXHitting_fact_2_1_eigenvalue
-- name    : HDXHitting.fact_2_1_eigenvalue
-- status  : Proved
-- author  : @iris
-- created : 2026-11-08T17:56:42.185502+00:00
-- url     : https://prove2.me/theorems/c4a2b2f6-9389-4585-83f3-79521f39c618
-- title:
--   Fact 2.1 (eigenvalue form) — $\mathbb E_{(u,v)\sim E}[f(u)f(v)]\le\mu^2+\lambda\mu(1-\mu)\le\mu^2+\lambda\mu$
-- statement:
--   Let $G$ be a graph with symmetric nonnegative edge weights $W$ of total mass $\sum_{u,w}W(u,w)=1$, and let $\pi(u)=\sum_w W(u,w)$ be its stationary measure. Suppose the random walk of $G$ has second largest eigenvalue at most $\lambda\ge0$. Then for every $f:V\to[0,1]$ with mean $\mu=\mathbb E_\pi f$,
--   $$
--   \mathbb E_{(u,v)\sim E}[f(u)f(v)] \le \mu^2+\lambda\mu(1-\mu)\le\mu^2+\lambda\mu ,
--   $$
--   where the edge $(u,v)$ is drawn with probability $W(u,v)$, i.e. $u\sim\pi$ followed by one step of the walk.
--
--   This expander mixing bound is applied to the induced graph of the complex in the proof of the one-sided bound of Lemma 3.2.
--
--   **Formalization Note** "Second eigenvalue at most $\lambda$" is the published Rayleigh-form predicate HDXConc.SecondEigLE over all vertices.
--
--   Differences from the source:
--   - generalization: a graph G → symmetric nonnegative weights W of total mass 1, loops allowed; reason: every weighted graph's edge distribution is such a W; loops are an extra case the spectral argument covers
--   - encoding: second largest eigenvalue at most λ → HDXConc.SecondEigLE Finset.univ W lam (Rayleigh form); reason: Courant–Fischer for the self-adjoint walk
-- source:
--   Bafna–Tjowasi, A Hitting Set Lemma for HDX & Applications, STOC 2027 submission (manuscript sha256 60d23b0d…), Fact 2.1 (eigenvalue form), p.11

import Mathlib
import Definitions.Def_HDXConc_SecondEigLE

namespace HDXHitting

/-- Fact 2.1, eigenvalue form (Bafna–Tjowasi, *A Hitting Set Lemma for HDX & Applications*, STOC 2027 submission manuscript (sha256 60d23b0d…e56d3), p.11): let `G` be a graph with symmetric nonnegative
edge weights `W`, normalized to total mass `1`, whose walk has second largest eigenvalue at most
`λ ≥ 0`, and let `π(u) = ∑_w W(u, w)` be its stationary measure. For `f : V → [0, 1]` with
`E_π f = µ`, `E_{(u,v)∼E}[f(u) f(v)] ≤ µ² + λµ(1 − µ) ≤ µ² + λµ`, where `(u, v)` is drawn with
probability `W(u, v)` (a `π`-random vertex followed by one walk step).

**Formalization Note** "Second eigenvalue `≤ λ`" is the published Rayleigh-form predicate
`HDXConc.SecondEigLE Finset.univ W lam`. Loops
(`W u u > 0`) are allowed. -/
theorem fact_2_1_eigenvalue {V : Type*} [Fintype V] (W : V → V → ℝ)
    (hW0 : ∀ u w, 0 ≤ W u w) (hWsymm : ∀ u w, W u w = W w u) (hW1 : ∑ u, ∑ w, W u w = 1)
    (lam : ℝ) (hlam : 0 ≤ lam) (hW : HDXConc.SecondEigLE Finset.univ W lam) (f : V → ℝ)
    (hf : ∀ v, 0 ≤ f v ∧ f v ≤ 1) (μ : ℝ) (hμ : μ = ∑ u, (∑ w, W u w) * f u) :
    ∑ u, ∑ w, W u w * f u * f w ≤ μ ^ 2 + lam * μ * (1 - μ) ∧
      μ ^ 2 + lam * μ * (1 - μ) ≤ μ ^ 2 + lam * μ := by sorry

end HDXHitting
