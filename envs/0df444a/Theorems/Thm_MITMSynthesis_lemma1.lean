-- Prove2me | Theorems.Thm_MITMSynthesis_lemma1
-- name    : MITMSynthesis.lemma1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-29T18:07:06.652683+00:00
-- url     : https://prove2.me/theorems/33c2fe20-9890-4d69-9972-bbde83ba596c
-- title:
--   Lemma 1 — meet in the middle: $U\in S_l \iff S^\dagger_{\lfloor l/2\rfloor}U\cap S_{\lceil l/2\rceil}\neq\emptyset$
-- statement:
--   Let $\mathcal G$ be an instruction set (closed under inverses), $n \in \mathbb N$, and let $S_i \subseteq U(2^n)$ be the set of unitaries implementable in depth $i$ over $\mathcal G$. For every unitary $U \in U(2^n)$ and every $l \in \mathbb N$, there is a circuit over $\mathcal G$ of depth $l$ implementing $U$ if and only if
--
--   $$
--   S^\dagger_{\lfloor l/2\rfloor}\, U \;\cap\; S_{\lceil l/2\rceil} \neq \emptyset,
--   $$
--
--   that is, iff there are $X \in S_{\lfloor l/2\rfloor}$ and $W \in S_{\lceil l/2\rceil}$ with $W = X^\dagger U$.
--
--   This is the observation behind the algorithm: circuits of depth $l$ can be found by generating only circuits of depth at most $\lceil l/2\rceil$ and looking for a collision.
--
--   **Formalization Note** $\lceil l/2\rceil$ and $\lfloor l/2\rfloor$ are the natural-number quotients `(l + 1) / 2` and `l / 2`.
--
--   Differences from the source:
--   - reading: there exists a circuit over G of depth l implementing U → U ∈ S_l, a product of exactly l elements of V_{n,G}; reason: the lemma's own S_i are the unitaries implementable in depth i, built on p. 6 as S_0 = {I}, S_i = V_{n,G}S_{i−1}
--   - encoding: S†_{⌊l/2⌋}U ∩ S_{⌈l/2⌉} ≠ ∅ → ∃ W ∈ S_{(l+1)/2}, ∃ X ∈ S_{l/2}, W = X† U; reason: the same set membership written out; ⌈l/2⌉ = (l+1)/2 and ⌊l/2⌋ = l/2 in ℕ
-- source:
--   Amy, Maslov, Mosca, Roetteler, A meet-in-the-middle algorithm for fast synthesis of depth-optimal quantum circuits, arXiv:1206.0758v3, Lemma 1, p. 5

import Mathlib
import Definitions.Def_MITMSynthesis_Gate
import Definitions.Def_MITMSynthesis_depthOneSet
import Definitions.Def_MITMSynthesis_S

namespace MITMSynthesis

/-- **Lemma 1 (meet in the middle).** Amy–Maslov–Mosca–Roetteler, arXiv:1206.0758v3, Lemma 1,
p. 5. Let `S_i` be the set of unitaries implementable in depth `i` over `G`. A unitary `U` is
implementable by a circuit over `G` of depth `l` iff `S_{⌊l/2⌋}† U ∩ S_{⌈l/2⌉} ≠ ∅`, i.e. iff some
`W ∈ S_{⌈l/2⌉}` equals `X† U` for some `X ∈ S_{⌊l/2⌋}`.
In ℕ, `⌈l/2⌉ = (l + 1) / 2` and `⌊l/2⌋ = l / 2`. -/
theorem lemma1 {n : ℕ} {G : Set Gate} (hG : IsInstructionSet G) (l : ℕ)
    (U : Matrix (Q n) (Q n) ℂ) (hU : U ∈ Matrix.unitaryGroup (Q n) ℂ) :
    U ∈ S (depthOneSet n G) l ↔
      ∃ W ∈ S (depthOneSet n G) ((l + 1) / 2), ∃ X ∈ S (depthOneSet n G) (l / 2),
        W = star X * U := by sorry

end MITMSynthesis
