-- Prove2me | Theorems.Thm_MinDegST_AddOne_lemma_16_9
-- name    : MinDegST.AddOne.lemma_16_9
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T06:54:09.063587+00:00
-- url     : https://prove2.me/theorems/b64a325a-1578-430c-b707-3d3226e42f07
-- title:
--   Lemma 16.9 — with θ = ⌈10n/f⌉ the path-encoding graph has an s–t flow of value Ω(f)
-- statement:
--   There is a universal constant $c>0$ such that: for every connected graph $G$ on $n$ nodes, threshold $k$ for which $G$ has a spanning tree of maximum degree at most $k$, forest $F$ of $G$ of maximum degree at most $k+1$ with $f\ge 2$ components, $\theta$-molecular decomposition $M$ of $F$ with $\theta=\lceil 10n/f\rceil$ and its reducible regions $\mathcal R$, the path-encoding graph has an $s$–$t$ flow $\varphi$ with
--   $$\operatorname{val}(\varphi)\ \ge\ c\cdot f .$$
--   This lower bound is what makes one maximum-flow call yield $\Omega(f)$ candidate augmenting chains (Lemma 16.1).
--
--   Differences from the source:
--   - generalization: the degree bound is Δ⋆(G) (feasible = max degree ≤ Δ⋆ + 1, slack = degree ≤ Δ⋆, saturated = Δ⋆ + 1) → any threshold k for which G has a spanning tree of maximum degree ≤ k, with feasible/slack/saturated relative to k; reason: Part I's convention (p. 4); the case k = Δ⋆(G) is the source's statement (G connected has a spanning tree of maximum degree Δ⋆ ≤ n − 1)
--   - encoding: an s–t flow of size Ω(f) → ∃ universal c > 0 (before G) and a real-valued flow φ (0 ≤ φ ≤ capacity, conservation) with value ≥ c·f; reason: explicit constant for Ω; real-valued flows are the paper's flows (capacities are integral)
--   - reading: a feasible forest F with f components → f ≥ 2; reason: standing assumption of §15 (θ = ⌈10n/f⌉ is defined for the current f ≥ 2); at f = 1, n = 1 there is no s–t path
--   - reading: §16.1: R⁻ → z⁻ for every z ∉ V(R) adjacent to R; tree-descending X⁻ → Y⁻ for Y ∈ B ∪ R → R⁻ → z⁻ only when z⁻ exists (z in no region); Y ranges over L ∪ 𝓡 (children after contracting regions); reason: no minus vertex exists for a node inside a region, and B is not defined in Part III
--   - reading: Definition 14.2 introduces θ in [1,n], but §16 sets θ = ⌈10n/f⌉ → the four decomposition clauses at θ = ⌈10n/f⌉ without imposing θ ≤ n; reason: the prescribed θ exceeds n when f < 10; the same clauses still apply and cover those source instances
-- source:
--   Bhattacharya, Farokhnejad, Saranurak, Wang, Faster Algorithms for Minimum Degree Spanning Tree, STOC 2027 submission (manuscript sha256 7d985d3b…), p. 43, Lemma 16.9

import Mathlib
import Definitions.Def_MinDegST_AddOne_Graph
import Definitions.Def_MinDegST_AddOne_Molecules
import Definitions.Def_MinDegST_AddOne_PathEncoding

namespace MinDegST.AddOne

/-- **Lemma 16.9** (threshold form). There is a universal constant `c > 0` such that: for every
connected simple graph `G` on `Fin n`, every threshold `k` for which `G` has a spanning tree of
maximum degree `≤ k`, every forest `F` of `G` of maximum degree `≤ k + 1` with `f ≥ 2` components,
the `θ`-molecular decomposition `M` with `θ = ⌈10n/f⌉` and its reducible regions `𝓡`, the
path-encoding graph admits an `s`–`t` flow of value at least `c · f`. -/
theorem lemma_16_9 :
    ∃ c : ℝ, 0 < c ∧
      ∀ (n : ℕ) (G : SimpleGraph (Fin n)) (k : ℕ) (F : SimpleGraph (Fin n))
        (M : Finset (Molecule n)) (𝓡 : Finset (Finset (Fin n))),
        G.Connected → HasSpanningTreeLE G k → IsForestOf G F → Feasible k F →
        2 ≤ numComponents F →
        IsThetaDecomp F k ⌈(10 * n : ℝ) / (numComponents F : ℝ)⌉₊ M →
        IsRegionsOf G F k M 𝓡 →
          ∃ φ : EncVtx n → EncVtx n → ℝ,
            IsEncFlow G F k ⌈(10 * n : ℝ) / (numComponents F : ℝ)⌉₊ M 𝓡 φ ∧
            c * (numComponents F : ℝ) ≤ encFlowValue F k M 𝓡 φ := by sorry

end MinDegST.AddOne
