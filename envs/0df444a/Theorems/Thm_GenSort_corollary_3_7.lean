-- Prove2me | Theorems.Thm_GenSort_corollary_3_7
-- name    : GenSort.corollary_3_7
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T03:30:17.421461+00:00
-- url     : https://prove2.me/theorems/14f84da1-eb3b-4392-9a1d-4455170c61ef
-- title:
--   Corollary 3.7 — with the §3.5 parameters, $\mathbb E_S[\#\text{bad edges in } H\setminus C_{\tau^*}] \le |L|w/((s+1)t) \le w/32$
-- statement:
--   Let $H$ be the current bipartite graph, with at most $2n$ left vertices and $w > 0$ bad edges, and run the protocol of §3.4 with the parameters of §3.5,
--   $$
--   s = \frac{2^{18}\, n\log n}{d}, \qquad t = \frac{d}{2^{12}\log n}.
--   $$
--   With $\tau^*$ the true relative order of the sampled multiset $S$,
--   $$
--   \mathbb E_S\big[\text{number of bad edges in } (H \setminus C_{\tau^*})\big] \le \frac{|L| \cdot w}{(s+1)t} \le \frac{w}{32}.
--   $$
--
--   Both inequalities are part of the statement.
--
--   Differences from the source:
--   - generalization: the current bipartite graph H of §3 → any finite bipartite instance with at most 2n left vertices, d ≥ 1; reason: the proof uses only st ≥ 64n and |L| ≤ 2n, and every current graph of §3 satisfies these hypotheses
--   - reading: s and t (real numbers) → ⌈2¹⁸ n log₂ n/d⌉ and ⌈d/(2¹² log₂ n)⌉; reason: §3.4 asks for positive integers; rounding up keeps st ≥ 64n
--   - reading: log n with no base fixed → log₂ n; reason: the paper never fixes the base; every constant on the path was checked for base 2
--   - reading: τ* and the tie rule of step 4 → any ordering monotone in π and any top-t selection; reason: the page leaves ties to arbitrary choice
--   - encoding: E_S over s uniformly random bad edges → requires w > 0; reason: with no bad edge the sampling step is undefined
--   - encoding: the vertex set V with a hidden ordering π → Fin n with a permutation π listing the vertices in increasing order, positions counted from 0; reason: a Lean convention that changes no instance
-- source:
--   Khanna, Putterman, Song, A Near-Optimal Generalized Sorting Algorithm, STOC 2027 submission (preprint of November 3, 2026, sha256 f1b5a9aa…), Corollary 3.7, p.10 (PDF p.12)

import Mathlib
import Definitions.Def_GenSort_badEdges
import Definitions.Def_GenSort_score
import Definitions.Def_GenSort_IsTopSelection
import Definitions.Def_GenSort_removalSet
import Definitions.Def_GenSort_IsTrueOrder
import Definitions.Def_GenSort_sampleExp
import Definitions.Def_GenSort_sPar
import Definitions.Def_GenSort_tPar

namespace GenSort

/-- **Corollary 3.7** (Khanna–Putterman–Song, *A Near-Optimal Generalized Sorting Algorithm*, STOC 2027 submission (preprint of November 3, 2026, sha256 f1b5a9aa…), §3.5, p.10, PDF p.12). Let `H` be the current bipartite graph, with at
most `2n` left vertices, and run the protocol with the §3.5 parameters `s = 2^18 n log n / d`,
`t = d / (2^12 log n)`. With `τ*` the true relative order of the sampled multiset `S`,
`E_S[number of bad edges in (H \ C_{τ*})] ≤ |L| · w / ((s + 1)t) ≤ w/32`.

**Formalization Note.** Both inequalities are stated. `s, t` are rounded up (`sPar`, `tPar`), `log`
is `log₂`; `τ*` and the tie rule `Q` are arbitrary as in Lemma 3.5. -/
theorem corollary_3_7 {d : ℕ} {n : ℕ} {L R : Type*} [Fintype L] [DecidableEq L] [DecidableEq R]
    (E : Finset (L × R)) (ℓ : L → Fin n) (r : R → Fin n) (π : Equiv.Perm (Fin n)) (hd : 0 < d) (hL : Fintype.card L ≤ 2 * n)
    (hw : 0 < (badEdges E ℓ r π).card)
    (τst : (Fin (sPar n d) → R) → Equiv.Perm (Fin (sPar n d)))
    (hτ : ∀ S, IsTrueOrder r π S (τst S)) (Q : (Fin (sPar n d) → R) → R → Finset L)
    (hQ : ∀ S, IsTopSelection E (score E S (τst S)) (tPar n d) (Q S)) :
    sampleExp (badEdges E ℓ r π) (sPar n d) (fun x =>
        ((badEdges (E \ removalSet E ℓ r π (fun i => (x i).2) (Q fun i => (x i).2)) ℓ r π).card :
          ℝ)) ≤
      (Fintype.card L : ℝ) * (badEdges E ℓ r π).card / ((sPar n d + 1) * tPar n d) ∧
    (Fintype.card L : ℝ) * (badEdges E ℓ r π).card / ((sPar n d + 1) * tPar n d) ≤
      ((badEdges E ℓ r π).card : ℝ) / 32 := by sorry

end GenSort
