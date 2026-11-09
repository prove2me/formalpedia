-- Prove2me | Theorems.Thm_HypRecov_theorem_1_1
-- name    : HypRecov.theorem_1_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T16:39:45.585552+00:00
-- url     : https://prove2.me/theorems/a3e55186-d849-4195-941b-7db80ced1cd1
-- title:
--   Theorem 1.1 — recovery of all $k$-crisp hyperedges at order $\min\{r,1+\lceil\log_2 k\rceil\}$ in $\widetilde O(nrk)$ bits
-- statement:
--   Let $H=(V,E)$ be a simple unweighted $r$-uniform hypergraph on $n$ vertices, $2\le r\le n$, observed through an anonymous stream of signed updates to the counts of $q$-vertex sets whose terminal counts are the complete $q$-projection of $H$.
--
--   There are one randomized one-pass linear sketch and absolute constants $C,c$ such that for all $2\le r\le n$, $k\ge 2$ and $0<\eta<1/4$, at observation order
--   $$q_{\mathrm{id}}=\min\{r,\ 1+\lceil\log_2 k\rceil\}:$$
--
--   1. states, coins and every machine's workspace, the decoder's output included, stay within $C\,nrk\,(1+\log_2(nrk/\eta))^c$ bits;
--   2. initialization, subtraction of two states and decoding take at most $C\,(nrk(1+\log_2(1/\eta)))^c$ steps, and an update with increment $\Delta$ at most $C\,(nrk(1+\log_2(1/\eta))(1+\mathrm{bitlen}\,\Delta))^c$;
--   3. the state depends on the stream only through its net counts, so the guarantee holds for every ordering;
--   4. for every such $H$ and every valid $q_{\mathrm{id}}$-projection stream of $H$, fixed before the coins, with probability at least $1-\eta$ the decoder outputs every edge of $\mathcal B_k(H)$ exactly once with all its vertices, and nothing else, together with a weighted hypergraph $\widehat H$ such that
--   $$\min\{\mathrm{cut}_H(S),k\}=\min\{\mathrm{cut}_{\widehat H}(S),k\}\qquad\text{for every }S\subseteq V.$$
--
--   By Theorem 1.2 the order $q_{\mathrm{id}}$ is the least at which the projection determines $\mathcal B_k(H)$ when $n\ge2r$.
--
--   **Formalization Note** The machine model and the reading of "linear sketch" are those of `SketchGuarantee`; the machines receive $m=\lceil1/\eta\rceil$.
--
--   Differences from the source:
--   - reading: "randomized one-pass linear sketch" → a state function sk ω y of the coins and the net count vector; init gives sk ω 0, an update (A, Δ) gives sk ω (y + Δ·1_A), a subtraction machine gives sk ω (y − y′); reason: how the paper uses linearity (Algorithm 2, p.21; Theorem 9.1) (paper.md decision 4)
--   - reading: a randomized one-pass algorithm, Õ(·) bits, polynomial time → the TM2 linear-sketch model of SketchGuarantee: one machine per role, coins uniform on Fin N → Fin M with M ≥ 1, space C·w·(1 + log₂(w/η))^c, time C·(w(1 + log₂(1/η))(1 + bit length))^c with absolute C, c; reason: the standard reading with absolute constants chosen before all parameters (paper.md decisions 3, 5, 6); the paper draws uniform field elements, which fair bits cannot produce exactly
--   - generalization: space and time of the algorithm on its inputs → the output stack counts toward space; the decoder's bounds hold on every state, valid or not; reason: the paper enforces all caps off the good event (p.12, p.18); the output O(nrk log n) bits fits the budget
--   - encoding: η, V = [n], vertex sets, the stream fixed before the coins and any ordering → m = ⌈1/η⌉₊ in binary, Fin n, vertex lists, σ quantified before the coins and the state sk ω (net σ); reason: 1/m ≤ η and log₂ m ≤ log₂(1/η) + 1; the state depends on the stream only through its net counts
--   - encoding: simple unweighted r-uniform hypergraph → a Finset of vertex sets of card r; reason: Lean convention
--   - reading: total working space O(w polylog(w/η)) bits → the update and subtraction machines may use the space budget plus the length of their own input (the state or states, the fragment and the increment); reason: an update must hold its supplied increment, whose bit length the paper lets the update time depend on, and the states it reads are within the budget
--   - encoding: a hypergraph representation Ĥ permitting weighted synthetic edges, cut_Ĥ(S) → a list of (vertex set, natural weight) pairs, cut_Ĥ(S) the total weight of the listed sets meeting both S and its complement; reason: the paper's Ĥ has synthetic weight-k edges and weight-1 original edges (Lemma 7.1)
-- source:
--   Zhang, Chen, Shen, Hypergraph Recovery from Anonymous Projection Streams, STOC 2027 submission (manuscript sha256 719dcfff4dc2eba2d8c5a3c51679a08cfb11f076546dea963c6376a2b9da2c82), Theorem 1.1, p.2 (PDF p.3); setting §1.1, p.1 (PDF p.2)

import Mathlib
import Definitions.Def_HypRecov_qid
import Definitions.Def_HypRecov_IsCorrect
import Definitions.Def_HypRecov_SketchGuarantee

namespace HypRecov

/-- **Theorem 1.1 (Recovery at the identifiability threshold).** Zhang, Chen, Shen, *Hypergraph
Recovery from Anonymous Projection Streams*, STOC 2027 submission (manuscript sha256 719dcfff…),
Theorem 1.1, p.2 (PDF p.3): "Let 0 < η < 1/4 and q_id = min{r, 1 + ⌈log₂ k⌉}. There is a randomized
one-pass linear sketch of an anonymous q_id-projection stream that recovers ℬ_k(H) with probability at
least 1 − η. Its total working space, including random descriptions and decoding workspace, is
O(nrk polylog(nrk/η)) bits. Preprocessing, per-fragment update and decoding take time polynomial in
n, r, k, log(1/η). Update time also accounts for the supplied increment's bit length. The same
successful state gives a hypergraph representation Ĥ, permitting weighted synthetic edges, such that
simultaneously for every S ⊆ V, min{cut_H(S), k} = min{cut_Ĥ(S), k}. The guarantee holds for each
fixed input stream, independently of its ordering. The stream is independent of the sketch coins."
Setting, §1.1, p.1: "Let H = (V, E) be a simple unweighted r-uniform hypergraph on n vertices, where
2 ≤ r ≤ n"; the target is ℬ_k(H) for k ≥ 2.

There are one linear sketch (four TM2 machines over `Bool` and coin sizes `N, M`) and absolute
constants `C, c` such that for all `2 ≤ r ≤ n`, `k ≥ 2` and `0 < η < 1/4`: the state, the coins read
by the initializer and every machine's workspace (output included) stay within
`C·nrk·(1 + log₂(nrk/η))^c` bits; initialization, subtraction and decoding take at most
`C·(nrk(1 + log₂(1/η)))^c` steps and an update with increment `Δ` at most
`C·(nrk(1 + log₂(1/η))(1 + bitlength Δ))^c`; and for every simple `r`-uniform `H` on `Fin n` and every
valid `q_id`-projection stream of `H`, fixed before the coins, with probability at least `1 − η` the
decoder outputs every edge of `ℬ_k(H)` exactly once, and nothing else, together with a weighted
hypergraph `Ĥ` with `min{cut_H(S), k} = min{cut_Ĥ(S), k}` for every `S`.

**Formalization Note.** The machine model, the reading of "linear sketch" and the budgets are those of
`SketchGuarantee` (paper.md decisions 3–6): `C`, `c`, the machines and the coin sizes are chosen before
`n, r, k, η`; the machines receive `m = ⌈1/η⌉₊`; the coins are uniform on `Fin N → Fin M` with
`M ≥ 1`. -/
theorem theorem_1_1 :
    ∃ (A : LinearSketch) (C c : ℕ), ∀ (n r k : ℕ) (η : ℝ), 2 ≤ r → r ≤ n → 2 ≤ k → 0 < η →
      η < 1 / 4 →
      SketchGuarantee A C c n r k (n * r * k) η (qid r k) (fun E out => IsCorrect E k out)
    := by sorry

end HypRecov
