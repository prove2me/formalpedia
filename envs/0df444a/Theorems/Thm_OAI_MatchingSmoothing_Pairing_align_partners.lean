-- Prove2me | Theorems.Thm_OAI_MatchingSmoothing_Pairing_align_partners
-- name    : OAI.MatchingSmoothing.Pairing.align_partners
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T04:29:54.160544+00:00
-- url     : https://prove2.me/theorems/ae4246f8-1337-4279-8c82-0ab5079909ac
-- title:
--   Matchings with the same internal edges on $U$ can be aligned on $U$ by a permutation fixing $U$
-- statement:
--   Let $\alpha$ be a finite set. A *pairing* of $\alpha$ (a perfect matching of the complete graph on $\alpha$) is a permutation $M$ of $\alpha$ that is a fixed-point-free involution: $M(M(a))=a$ and $M(a)\ne a$ for all $a$. Here $M(a)$ is the partner of $a$. A permutation $p$ of $\alpha$ relabels $M$ into the pairing $pMp^{-1}$, which matches $p(a)$ with $p(M(a))$.
--
--   Let $U\subseteq\alpha$, and let $M,N$ be pairings with the same internal edges on $U$: for all $a,b\in U$, $M(a)=b$ if and only if $N(a)=b$. Then some permutation fixing $U$ pointwise relabels $M$ so that it gives every vertex of $U$ its $N$-partner:
--
--   $$
--   \exists\,p\in\mathrm{Sym}(\alpha):\qquad p(a)=a\quad\text{and}\quad (pMp^{-1})(a)=N(a)\qquad\text{for all }a\in U .
--   $$
--
--   The edges of $M$ inside $U$ are those of $N$ by hypothesis. The content of the lemma is that the vertices of $U$ matched to the outside can be redirected to their $N$-partners by permuting only vertices outside $U$. A second step aligns the remaining edges away from $U$. Together they show that two pairings with the same internal pattern on $U$ are conjugate under the pointwise stabiliser of $U$. Consequently, a function of pairings that is invariant under that stabiliser depends only on the internal pattern on $U$.
--
--   **Formalization Note** Pairings are `Pairing α`, the subtype of `Equiv.Perm α` consisting of fixed-point-free involutions. The relabelled pairing $pMp^{-1}$ is `relabel p M`, and the hypothesis is `SameInternal U M N`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/MatchingPSD/Pairings.lean#L129-L184

import Mathlib
import Definitions.Def_MatchingPSD
import Definitions.Def_OAI_Combinatorics_MatchingPSD_EdgeProducts
import Definitions.Def_OAI_Combinatorics_MatchingPSD_Pairings

open OAI OAI.MatchingSmoothing OAI.MatchingSmoothing.Pairing
universe u_1 u_2
variable {α : Type u_2}

theorem OAI.MatchingSmoothing.Pairing.align_partners [Fintype α] [DecidableEq α]
    (U : Finset α) (M N : Pairing α) (hMN : SameInternal U M N) :
    ∃ p : Equiv.Perm α, (∀ a ∈ U, p a = a) ∧
      ∀ a ∈ U, (relabel p M).1 a = N.1 a := by sorry
