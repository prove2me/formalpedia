-- Prove2me | Theorems.Thm_NicerEars_TJoin_theorem_18
-- name    : NicerEars.TJoin.theorem_18
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T06:30:43.450673+00:00
-- url     : https://prove2.me/theorems/b5245598-7230-4891-8b7c-e84e516739e9
-- title:
--   Theorem 18 — the earmuff theorem: µ(G,M) = min{|M| − Σ sur(W)}
-- statement:
--   Let $G$ be a graph and $M$ an eardrum in $G$ with $\mathcal P_f\ne\emptyset$ for all $f\in M$. Then the maximum size of an earmuff is
--   $$\mu(G,M)=\min\Bigl\{\,|M|-\sum_{W\in\mathcal W}\mathrm{sur}(W)\ :\ \mathcal W\text{ is a partition of }V(G)\setminus V_M\Bigr\},$$
--   where $\mathrm{sur}(W)=|\{f\in M:U_f\subseteq W\}|-(|W|-1)$ and $U_f$ is the set of endpoints of paths in $\mathcal P_f$.
--
--   The minimizing partition supplies the dual solution behind the lower bound of Theorem 20.
--
--   **Formalization Note.** The algorithmic claim ($O(|V(G)||E(G)|)$ time) is not formalized. The equality is stated as: the bound holds for every partition of $V(G)\setminus V_M$ and some partition attains it, in $\mathbb Z$. The paper's standing assumption $V(G)\setminus V_M\neq\emptyset$ (p. 15) is not a hypothesis: it follows when $M\ne\emptyset$ and every $\mathcal P_f\ne\emptyset$, and when $M=\emptyset$ both sides are $0$ for every graph.
-- source:
--   Sebő and Vygen, Shorter tours by nicer ears, arXiv:1201.1870v3, p. 15, Theorem 18 (Definition 12, p. 11; surplus, p. 15)

import Mathlib
import Definitions.Def_NicerEars_TJoin_Earmuff

namespace NicerEars.TJoin

open Finset

variable {V E : Type} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]

/-- Theorem 18 (p. 15), the earmuff min-max: for an eardrum `M` in `G` with `𝒫_f ≠ ∅` for all
`f ∈ M`,
`µ(G, M) = min { |M| − Σ_{W ∈ 𝒲} sur(W) : 𝒲 a partition of V(G) ∖ V_M }`,
stated as: the bound holds for every partition, and some partition attains it. -/
theorem theorem_18 (G : Graph V E) (M : Finset (Finset V)) (hM : IsEardrum G M)
    (hP : ∀ f ∈ M, (PathsThrough G f).Nonempty) :
    (∀ 𝒲 : Finpartition (univ \ VM M), (mu G M : ℤ) ≤ #M - ∑ W ∈ 𝒲.parts, surplus G M W) ∧
    ∃ 𝒲 : Finpartition (univ \ VM M), (mu G M : ℤ) = #M - ∑ W ∈ 𝒲.parts, surplus G M W := by sorry

end NicerEars.TJoin
