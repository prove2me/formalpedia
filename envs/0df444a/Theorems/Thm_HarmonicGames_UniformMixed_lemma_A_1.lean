-- Prove2me | Theorems.Thm_HarmonicGames_UniformMixed_lemma_A_1
-- name    : HarmonicGames.UniformMixed.lemma_A_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T06:45:58.708104+00:00
-- url     : https://prove2.me/theorems/7595087c-c683-4a6a-9e51-6114bb4a466b
-- title:
--   Lemma A.1 — the sum of $\delta_0^*\hat X$ over a set of profiles is minus the flow leaving the set
-- statement:
--   Let $\mathcal G = (E, A)$ be the game graph of a finite game (nodes: strategy profiles; $p, q$ adjacent iff they differ in exactly one player's strategy), $C_1$ the space of edge flows on it with the inner product $\langle X, Y\rangle_1 = \tfrac12 \sum_{(p,q)\in A} X(p,q)Y(p,q)$, and $\delta_0^* : C_1 \to C_0$ the adjoint of the combinatorial gradient $\delta_0$. For every edge flow $\hat X \in C_1$ and every set of strategy profiles $\hat S \subset E$, with complement $\hat S^c = E \setminus \hat S$,
--
--   $$
--   \sum_{p \in \hat S} (\delta_0^* \hat X)(p) = -\sum_{p \in \hat S} \sum_{q \in \hat S^c} \hat X(p,q).
--   $$
--
--   The identity expresses the total divergence over a set of nodes as the net flow across its boundary; in the paper it turns the harmonic condition $\delta_0^* D u = 0$ into the payoff identity of Lemma 5.2.
--
--   **Formalization Note** $\delta_0^*$ is Mathlib's `LinearMap.adjoint` for the inner products (7), including the factor $\tfrac12$; without it the left side would be off by a factor $2$. $\hat S$ is a `Finset` of profiles.
-- source:
--   Candogan, Menache, Ozdaglar, Parrilo, Flows and Decompositions of Games: Harmonic and Potential Games, arXiv:1005.2405v2, p. 43, Appendix A, Lemma A.1

import Mathlib
import Definitions.Def_HarmonicGames_Decomposition_Games
import Definitions.Def_HarmonicGames_GenericPure_Games

namespace HarmonicGames.UniformMixed

/-- **Lemma A.1** (p. 43): for every edge flow `X̂ ∈ C1` on the game graph and every set of
strategy profiles `Ŝ ⊂ E`, `∑_{p ∈ Ŝ} (δ0* X̂)(p) = -∑_{p ∈ Ŝ} ∑_{q ∈ Ŝᶜ} X̂(p,q)`, where
`δ0*` is the adjoint of the combinatorial gradient for the inner products (7). -/
theorem lemma_A_1 {ι : Type} [Fintype ι] [DecidableEq ι] (E : ι → Type) [∀ m, Fintype (E m)]
    [∀ m, DecidableEq (E m)]
    (X : HarmonicGames.Decomposition.Flow E) (S : Finset (∀ k, E k)) :
    ∑ p ∈ S, (LinearMap.adjoint (HarmonicGames.Decomposition.delta0 (HarmonicGames.Decomposition.gameGraph E)) X) p = -∑ p ∈ S, ∑ q ∈ Sᶜ, X p q := by sorry

end HarmonicGames.UniformMixed
