-- Prove2me | Theorems.Thm_GenSort_lemma_3_5
-- name    : GenSort.lemma_3_5
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T03:29:05.737612+00:00
-- url     : https://prove2.me/theorems/ed62460d-faf3-4ad9-b4af-9c3b15700b7f
-- title:
--   Lemma 3.5 — $\mathbb E_S[\#\text{bad edges in } H \setminus C_{\tau^*}] \le |L|\,w/((s+1)t)$
-- statement:
--   Let $H$ be a bipartite graph with left part $L$, right part $R$ and edge set $E$, with $w > 0$ bad edges, and let $s, t$ be positive integers. Run the error isolation protocol of §3.4: sample $s$ uniformly random bad edges with replacement and let $S = (S_1, \dots, S_s)$ be their right endpoints; mark every left vertex with an incorrectly oriented edge to a vertex of $S$; for an ordering $\tau$ of $S$, give each left vertex the score $\mathrm{Score}_\tau$, let every right vertex select its $t$ highest-score neighbours $Q_v$, and form $C_\tau$. For each sampled multiset $S$ let $\tau^*$ be the ordering of $S$ induced by the true permutation $\pi$. Then
--   $$
--   \mathbb E_S\big[\text{number of bad edges in } (H \setminus C_{\tau^*})\big] \le \frac{|L| \cdot w}{(s + 1)t}.
--   $$
--
--   This is the key lemma: removing $C_{\tau^*}$ cuts the number of errors by a large factor once $(s+1)t \ge 32|L|$.
--
--   Differences from the source:
--   - generalization: the current bipartite graph H of §3 → any finite bipartite instance (L, R, E ⊆ L × R, original-vertex maps ℓ, r); reason: the proof on the page uses only the bipartite structure, and every current graph H of §3 is such an instance
--   - reading: the ordering induced by π, and ties broken arbitrarily → any ordering monotone in π and any top-t selection, both may depend on S; reason: the page leaves ties to arbitrary choice; the universal reading is the stronger one
--   - encoding: E_S over s uniformly random bad edges → requires w > 0; reason: with no bad edge the sampling step is undefined
--   - encoding: the multiset S → a sequence indexed by {1, …, s}, ranks given by a permutation of the indices; reason: repeated samples are separate entries of the multiset
--   - encoding: the vertex set V with a hidden ordering π → Fin n with a permutation π listing the vertices in increasing order, positions counted from 0; reason: a Lean convention that changes no instance
-- source:
--   Khanna, Putterman, Song, A Near-Optimal Generalized Sorting Algorithm, STOC 2027 submission (preprint of November 3, 2026, sha256 f1b5a9aa…), Lemma 3.5, p.8 (PDF p.10), with the protocol of §3.4, pp.7–8

import Mathlib
import Definitions.Def_GenSort_badEdges
import Definitions.Def_GenSort_score
import Definitions.Def_GenSort_IsTopSelection
import Definitions.Def_GenSort_removalSet
import Definitions.Def_GenSort_IsTrueOrder
import Definitions.Def_GenSort_sampleExp

namespace GenSort

/-- **Lemma 3.5** (Khanna–Putterman–Song, *A Near-Optimal Generalized Sorting Algorithm*, STOC 2027 submission (preprint of November 3, 2026, sha256 f1b5a9aa…), §3.4, p.8, PDF p.10). Run the error isolation protocol with positive
integers `s, t` on a bipartite graph `H` with current edge set `E ⊆ L × R` and `w > 0` bad edges:
`S = (S_1, …, S_s)` are the right endpoints of `s` independent uniformly random bad edges. For
each sampled multiset `S` let `τ*` be the ordering of `S` induced by the true permutation `π`.
Then
`E_S[number of bad edges in (H \ C_{τ*})] ≤ |L| · w / ((s + 1)t)`.

**Formalization Note.** `τ*` is any ordering monotone in `π` (ties either way) and `Q` any top-`t`
selection for the scores under `τ*`; both may depend on `S`. `|L|` is `Fintype.card L`. -/
theorem lemma_3_5 {n : ℕ} {L R : Type*} [Fintype L] [DecidableEq L] [DecidableEq R]
    (E : Finset (L × R)) (ℓ : L → Fin n) (r : R → Fin n) (π : Equiv.Perm (Fin n)) (s t : ℕ) (hs : 0 < s) (ht : 0 < t) (hw : 0 < (badEdges E ℓ r π).card)
    (τst : (Fin s → R) → Equiv.Perm (Fin s)) (hτ : ∀ S, IsTrueOrder r π S (τst S))
    (Q : (Fin s → R) → R → Finset L) (hQ : ∀ S, IsTopSelection E (score E S (τst S)) t (Q S)) :
    sampleExp (badEdges E ℓ r π) s (fun x =>
        ((badEdges (E \ removalSet E ℓ r π (fun i => (x i).2) (Q fun i => (x i).2)) ℓ r π).card :
          ℝ)) ≤
      (Fintype.card L : ℝ) * (badEdges E ℓ r π).card / ((s + 1) * t) := by sorry

end GenSort
