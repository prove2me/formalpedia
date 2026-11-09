-- Prove2me | Theorems.Thm_HypRecov_theorem_6_4
-- name    : HypRecov.theorem_6_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T16:39:56.860212+00:00
-- url     : https://prove2.me/theorems/eb597d1b-bba3-42d6-bc0a-856cba531273
-- title:
--   Theorem 6.4 — simultaneous exact order and target space ($k\ge 3$)
-- statement:
--   There are one randomized one-pass linear sketch and absolute constants $C,c$ such that for all $2\le r\le n$, $k\ge3$ and $0<\eta<1$, at observation order $q_{\mathrm{id}}=\min\{r,1+\lceil\log_2k\rceil\}$: states, coins and every machine's workspace stay within $C\,nrk\,(1+\log_2(nrk/\eta))^c$ bits; initialization, subtraction and decoding take at most $C\,(nrk(1+\log_2(1/\eta)))^c$ steps, and an update with increment $\Delta$ at most $C\,(nrk(1+\log_2(1/\eta))(1+\mathrm{bitlen}\,\Delta))^c$; and for every simple $r$-uniform $H$ on $n$ vertices and every valid $q_{\mathrm{id}}$-projection stream of $H$, fixed before the coins, with probability at least $1-\eta$ the decoder outputs every edge of $\mathcal B_k(H)$ exactly once and nothing else.
--
--   This is the case $k\ge3$ of Theorem 1.1 without the representation $\widehat H$.
--
--   Differences from the source:
--   - reading: a randomized one-pass algorithm, Õ(·) bits, polynomial time → the TM2 linear-sketch model of SketchGuarantee: one machine per role, coins uniform on Fin N → Fin M with M ≥ 1, space C·w·(1 + log₂(w/η))^c, time C·(w(1 + log₂(1/η))(1 + bit length))^c with absolute C, c; reason: the standard reading with absolute constants chosen before all parameters (paper.md decisions 3, 5, 6); the paper draws uniform field elements, which fair bits cannot produce exactly
--   - generalization: the theorem does not say "linear" → the state is a function of the coins and the net counts, updates are additive, and a subtraction machine exists; reason: the construction is linear (modular and field registers, random description carried unchanged); the goal's linear-sketch reading needs it (paper.md decision 4)
--   - generalization: space and time of the algorithm on its inputs → the output stack counts toward space; the decoder's bounds hold on every state, valid or not; reason: the paper enforces all caps off the good event (p.12, p.18); the output O(nrk log n) bits fits the budget
--   - encoding: η, V = [n], vertex sets, the stream fixed before the coins and any ordering → m = ⌈1/η⌉₊ in binary, Fin n, vertex lists, σ quantified before the coins and the state sk ω (net σ); reason: 1/m ≤ η and log₂ m ≤ log₂(1/η) + 1; the state depends on the stream only through its net counts
--   - reading: success probability at least 1 − η (no range printed) → every 0 < η < 1; reason: the stronger reading; any η ∈ (0, 1) is meaningful
--   - reading: total working space O(w polylog(w/η)) bits → the update and subtraction machines may use the space budget plus the length of their own input (the state or states, the fragment and the increment); reason: an update must hold its supplied increment, whose bit length the paper lets the update time depend on, and the states it reads are within the budget
--   - reading: "every simple unweighted r-uniform terminal hypergraph in the stated … model", for the k of §6 → 2 ≤ r ≤ n and 3 ≤ k; reason: the stated model is that of §1.1 (p.1: "2 ≤ r ≤ n"), and §6 (p.12) considers k ≥ 3, k = 2 being Theorem D.1
-- source:
--   Zhang, Chen, Shen, Hypergraph Recovery from Anonymous Projection Streams, STOC 2027 submission (manuscript sha256 719dcfff4dc2eba2d8c5a3c51679a08cfb11f076546dea963c6376a2b9da2c82), Theorem 6.4, pp.15–16 (PDF pp.16–17)

import Mathlib
import Definitions.Def_HypRecov_qid
import Definitions.Def_HypRecov_IsCorrect
import Definitions.Def_HypRecov_SketchGuarantee

namespace HypRecov

/-- **Theorem 6.4 (Simultaneous exact order and target space), the case `k ≥ 3` of Theorem 1.1.**
Zhang, Chen, Shen, *Hypergraph Recovery from Anonymous Projection Streams*, STOC 2027 submission
(manuscript sha256 719dcfff…), Theorem 6.4, pp.15–16 (PDF pp.16–17): "For every simple unweighted
r-uniform terminal hypergraph in the stated anonymous complete-projection turnstile model, one pass at
order q_id = min{r, 1 + ⌈log₂ k⌉} suffices for automatic exact recovery of ℬ_k(H), with probability
at least 1 − η, uniform polynomial setup/update/decoding time, and Õ(nrk) bits including stored
randomness and decoding workspace. The logarithmic factors include the precision and failure
probability from the measurement construction. Update time also accounts for the increment's bit
length."

There are one linear sketch and constants `C, c` such that for all `2 ≤ r ≤ n`, `k ≥ 3` and
`0 < η < 1`, at order `q_id`, with space `C·nrk·(1 + log₂(nrk/η))^c` bits and time
`C·(nrk(1 + log₂(1/η)))^c` (update: times the increment's bit length inside the power), the decoder
outputs exactly `ℬ_k(H)`, each edge once, with probability at least `1 − η` for every valid stream.

**Formalization Note.** The machine model is that of `SketchGuarantee` with `w = nrk`. The theorem
prints no range for `η`; every `η ∈ (0, 1)` is covered. The linear-sketch clauses are included because
the construction is linear (all registers are modular or field sums, p.16). -/
theorem theorem_6_4 :
    ∃ (A : LinearSketch) (C c : ℕ), ∀ (n r k : ℕ) (η : ℝ), 2 ≤ r → r ≤ n → 3 ≤ k → 0 < η → η < 1 →
      SketchGuarantee A C c n r k (n * r * k) η (qid r k) (fun E out => IsCorrectList E k out)
    := by sorry

end HypRecov
