-- Prove2me | Theorems.Thm_GraphonCheeger_Supplement_theorem_6_9
-- name    : GraphonCheeger.Supplement.theorem_6_9
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T08:38:26.551418+00:00
-- url     : https://prove2.me/theorems/2fac1809-6dcb-4538-b406-fc53a422fea4
-- title:
--   Theorem 6.9 — modularity is $\rho$-estimable
-- statement:
--   For all $\varepsilon,\rho>0$ there exists a positive integer $k=k(\varepsilon,\rho)$ such that for every graph $G$ with $|G|\ge k$ and edge density $\rho_G=e(G)/\binom{|G|}{2}\ge\rho$,
--   $$
--   \mathbb P\bigl(|q^*(G)-q^*(\mathbb G(k,G))|>\varepsilon\bigr)<\varepsilon,
--   $$
--   where $\mathbb G(k,G)$ is the subgraph of $G$ induced on $k$ vertices chosen uniformly at random without replacement. That is, modularity is $\rho$-estimable.
--
--   Modularity of a dense graph can be estimated from a bounded-size random sample, although it is not estimable without the density restriction.
--
--   **Formalization Note** Graphs are simple graphs on `Fin n` ($q^*$ is invariant under isomorphism). The probability is the number of $k$-subsets $S$ of the vertex set with $|q^*(G)-q^*(G[S])|>\varepsilon$, divided by $\binom nk$.
--
--   Differences from the source:
--   - encoding: every G ∈ 𝒢 (finite simple graphs up to isomorphism) and the random induced subgraph 𝔾(k, G) → G : SimpleGraph (Fin n); the proportion of k-subsets S with |q*(G) − q*(G.induce S)| > ε; reason: q* is invariant under isomorphism, and a uniformly random k-subset has the law of sampling k vertices without replacement
-- source:
--   Janson, Lo, McDiarmid, Skeja, Skerman, Graphon Colourings and Limits of Graph Partitions, arXiv:2610.38599 (held version, sha256 3d198813a65d248922299a3380e10f238dbc5dcd3be060f7810b462bd5d3d10f), Theorem 6.9, p.77 (PDF p.77)

import Mathlib
import Definitions.Def_GraphonCheeger_Supplement_graphModularity

open Classical

namespace GraphonCheeger.Supplement

/-- Theorem 6.9, p.77 (Janson, Lo, McDiarmid, Skeja, Skerman, *Graphon Colourings and Limits of Graph Partitions*,
arXiv:2610.38599 (held version, sha256 3d198813…)): for all `ε, ρ > 0` there exists a positive integer `k = k(ε, ρ)` such that
for every graph `G` with `|G| ≥ k` and `ρ_G ≥ ρ`,
`P(|q*(G) − q*(G(k, G))| > ε) < ε` (6.20); i.e. modularity is `ρ`-estimable.

**Formalization Note.** Graphs are simple graphs on `Fin n` (every finite graph up to isomorphism;
`q*` is invariant under isomorphism). `ρ_G = e(G)/C(|G|, 2)` (`edgeDensityG`, p.82). `G(k, G)` is
the subgraph induced on a uniformly random `k`-subset `S` of the vertices, so the probability is the
number of `k`-subsets `S` with `|q*(G) − q*(G[S])| > ε` divided by `C(n, k)`. The "i.e."
clause is Definition 6.1 restated. -/
theorem theorem_6_9 :
    ∀ ε : ℝ, 0 < ε → ∀ ρ : ℝ, 0 < ρ → ∃ k : ℕ, 0 < k ∧
      ∀ (n : ℕ) (G : SimpleGraph (Fin n)), k ≤ n → ρ ≤ edgeDensityG G →
        ((Finset.univ.filter (fun S : Finset (Fin n) => S.card = k ∧
            ε < |modularity G - modularity (G.induce (S : Set (Fin n)))|)).card : ℝ) /
          (n.choose k : ℝ) < ε := by sorry

end GraphonCheeger.Supplement
