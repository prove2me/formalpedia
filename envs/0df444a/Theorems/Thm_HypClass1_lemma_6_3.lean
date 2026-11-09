-- Prove2me | Theorems.Thm_HypClass1_lemma_6_3
-- name    : HypClass1.lemma_6_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T07:35:52.275714+00:00
-- url     : https://prove2.me/theorems/e5e3ccfc-be13-4ac1-85db-9e590c9718b1
-- title:
--   Lemma 6.3 ([24, Lemma 4.4]) — a regular spanning subgraph of $B\cup R$ containing $R$
-- statement:
--   There is a constant $\alpha_0 \in (0,1]$ such that the following holds. Let $\alpha, p, \gamma \in [0,1]$ and $n \ge 1$ with $\alpha \le \alpha_0$ and $\alpha pn \ge 1$. If $R$ and $B$ are disjoint bipartite graphs with parts $X, Y$, $|X| = |Y| = n$, such that $B$ is $(\alpha,p,n)$-pseudorandom and $R$ is $(\gamma\pm\alpha)pn$-regular, then there is a regular spanning subgraph $G \subseteq B \cup R$ with $R \subseteq G$.
--
--   This is a max-flow result of Kang, Kelly, Kühn, Methuku and Osthus, quoted by the paper; it is a step of the algorithm of Lemma 6.1.
--
--   **Formalization Note** Both parts are `Fin n`; "regular spanning" means every vertex of $X \cup Y$ has the same degree $d$ in $G$.
--
--   Differences from the source: none.
-- source:
--   Chatterjee, Ferber, Sales, Shurman, Almost Every 3-Uniform Hypergraph is Class 1, manuscript (STOC 2027 submission, version of 2026-11-03, sha256 ce3bba9d…), Lemma 6.3 (quoting [24] Lemma 4.4), p.16

import Mathlib
import Definitions.Def_HypClass1_IsPseudorandomBip
import Definitions.Def_HypClass1_IsAlmostRegularBip

namespace HypClass1

/-- **Lemma 6.3 ([24, Lemma 4.4], as quoted: a regular spanning subgraph containing R).** Chatterjee, Ferber, Sales, Shurman, *Almost Every 3-Uniform Hypergraph is Class 1*, manuscript
(STOC 2027 submission, version of 2026-11-03, sha256 ce3bba9d…),
Lemma 6.3, p.16: "There exists a positive constant α₀ ∈ (0, 1] such that the following holds: Let
α, p, γ ∈ [0, 1] and n ≥ 1 such that α ≤ α₀ and αpn ≥ 1. If R and B are disjoint bipartite graphs on
the vertex set X, Y with |X| = |Y| = n such that B is (α, p, n)-pseudorandom and R is
(γ ± α)pn-regular, then there exists a regular spanning subgraph G ⊆ B ∪ R such that R ⊆ G."

**Formalization Note.** Both parts are `Fin n`. "Regular spanning subgraph": a subgraph `G` of `B ∪ R` on
all of `X ∪ Y` in which every vertex has the same degree `d` (`d = 0` allowed). -/
theorem lemma_6_3 :
    ∃ α₀ : ℝ, 0 < α₀ ∧ α₀ ≤ 1 ∧ ∀ α p γ : ℝ, 0 ≤ α → α ≤ 1 → 0 ≤ p → p ≤ 1 → 0 ≤ γ → γ ≤ 1 →
      ∀ n : ℕ, 1 ≤ n → α ≤ α₀ → 1 ≤ α * p * n →
      ∀ R B : Finset (Fin n × Fin n), Disjoint R B →
        IsPseudorandomBip α p Finset.univ Finset.univ B →
        IsAlmostRegularBip γ α p Finset.univ Finset.univ R →
        ∃ G : Finset (Fin n × Fin n), G ⊆ B ∪ R ∧ R ⊆ G ∧
          ∃ d : ℕ, (∀ x : Fin n, ldeg G x = d) ∧ ∀ y : Fin n, rdeg G y = d := by sorry

end HypClass1
