-- Prove2me | Theorems.Thm_HypRecov_theorem_D_1
-- name    : HypRecov.theorem_D_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T16:40:03.737199+00:00
-- url     : https://prove2.me/theorems/1479a477-ee84-4710-9ded-7812c6ed4e57
-- title:
--   Theorem D.1 — automatic recovery of bridge hyperedges ($k=2$)
-- statement:
--   **(a) Recovery.** There are one randomized one-pass linear sketch and absolute constants $C,c$ such that for all $2\le r\le n$ and $0<\eta<1$, at observation order $q=2$: states, coins and every machine's workspace stay within $C\,nr\,(1+\log_2(nr/\eta))^c$ bits; initialization, subtraction and decoding take at most $C\,(nr(1+\log_2(1/\eta)))^c$ steps, and an update with increment $\Delta$ at most $C\,(nr(1+\log_2(1/\eta))(1+\mathrm{bitlen}\,\Delta))^c$; and for every simple $r$-uniform $H$ on $n$ vertices and every valid pair-projection stream of $H$, fixed before the coins, with probability at least $1-\eta$ the decoder outputs every edge of $\mathcal B_2(H)$ exactly once and nothing else.
--
--   **(b) Optimality of the order.** If $n\ge 2r$, there are two simple $r$-uniform hypergraphs on $n$ vertices with the same $1$-projection (vertex degrees) and different $\mathcal B_2$; so order $1$ does not suffice.
--
--   This is the case $k=2$ of Theorem 1.1, the recovery of all bridge hyperedges from pair counts.
--
--   Differences from the source:
--   - reading: a randomized one-pass algorithm, Õ(·) bits, polynomial time → the TM2 linear-sketch model of SketchGuarantee: one machine per role, coins uniform on Fin N → Fin M with M ≥ 1, space C·w·(1 + log₂(w/η))^c, time C·(w(1 + log₂(1/η))(1 + bit length))^c with absolute C, c; reason: the standard reading with absolute constants chosen before all parameters (paper.md decisions 3, 5, 6); the paper draws uniform field elements, which fair bits cannot produce exactly
--   - generalization: the theorem does not say "linear" → the state is a function of the coins and the net counts, updates are additive, and a subtraction machine exists; reason: the construction is linear (modular and field registers, random description carried unchanged); the goal's linear-sketch reading needs it (paper.md decision 4)
--   - generalization: space and time of the algorithm on its inputs → the output stack counts toward space; the decoder's bounds hold on every state, valid or not; reason: the paper enforces all caps off the good event (p.12, p.18); the output O(nrk log n) bits fits the budget
--   - encoding: η, V = [n], vertex sets, the stream fixed before the coins and any ordering → m = ⌈1/η⌉₊ in binary, Fin n, vertex lists, σ quantified before the coins and the state sk ω (net σ); reason: 1/m ≤ η and log₂ m ≤ log₂(1/η) + 1; the state depends on the stream only through its net counts
--   - reading: success probability at least 1 − η (no range printed) → every 0 < η < 1; reason: the stronger reading; any η ∈ (0, 1) is meaningful
--   - reading: "Its observation order is q = 2, which is optimal for k = 2 when n ≥ 2r" → two r-uniform hypergraphs with equal 1-projections and different ℬ₂; reason: the only smaller order is q = 1; optimality means it does not determine ℬ₂ (Theorem 3.4)
--   - reading: "on n vertices, where r ≥ 2" → 2 ≤ r ≤ n; reason: the paper's standing assumption 2 ≤ r ≤ n (§1.1, p.1)
--   - reading: total working space O(w polylog(w/η)) bits → the update and subtraction machines may use the space budget plus the length of their own input (the state or states, the fragment and the increment); reason: an update must hold its supplied increment, whose bit length the paper lets the update time depend on, and the states it reads are within the budget
-- source:
--   Zhang, Chen, Shen, Hypergraph Recovery from Anonymous Projection Streams, STOC 2027 submission (manuscript sha256 719dcfff4dc2eba2d8c5a3c51679a08cfb11f076546dea963c6376a2b9da2c82), Theorem D.1, p.37 (PDF p.38)

import Mathlib
import Definitions.Def_HypRecov_crisp
import Definitions.Def_HypRecov_IsCorrect
import Definitions.Def_HypRecov_SketchGuarantee

namespace HypRecov

/-- **Theorem D.1 (Automatic recovery of bridge hyperedges), the case `k = 2` of Theorem 1.1.** Zhang,
Chen, Shen, *Hypergraph Recovery from Anonymous Projection Streams*, STOC 2027 submission (manuscript
sha256 719dcfff…), Theorem D.1, p.37 (PDF p.38): "Let H be a simple r-uniform hypergraph on n
vertices, where r ≥ 2. From an integer stream whose terminal state is the complete anonymous pair
projection of H, a randomized one-pass algorithm recovers ℬ_2(H) using Õ(nr) bits, including all
random descriptions and decoding workspace, in polynomial time. Its success probability is at least
1 − η. Its observation order is q = 2, which is optimal for k = 2 when n ≥ 2r."

(a) There are one linear sketch (four TM2 machines and coin sizes) and constants `C, c` such that for
all `2 ≤ r ≤ n` and `0 < η < 1`, at order `q = 2` (and `k = 2`), with space `C·nr·(1 + log₂(nr/η))^c`
bits and time `C·(nr(1 + log₂(1/η)))^c` (update: times the increment's bit length inside the power),
the decoder outputs exactly `ℬ_2(H)`, each edge once, with probability at least `1 − η` for every
valid pair-projection stream. (b) For `n ≥ 2r` order `1` does not suffice: two `r`-uniform hypergraphs
on `Fin n` have the same `1`-projection and different `ℬ_2`.

**Formalization Note.** The machine model is that of `SketchGuarantee` with `w = nr`. The theorem
prints no range for `η`; every `η ∈ (0, 1)` is covered. The linear-sketch clauses (state a function of
the net counts, subtraction machine) are included because the construction is linear (Lemma B.1, the
pair registers modulo a prime, p.38). -/
theorem theorem_D_1 :
    (∃ (A : LinearSketch) (C c : ℕ), ∀ (n r : ℕ) (η : ℝ), 2 ≤ r → r ≤ n → 0 < η → η < 1 →
      SketchGuarantee A C c n r 2 (n * r) η 2 (fun E out => IsCorrectList E 2 out)) ∧
    ∀ n r : ℕ, 2 ≤ r → 2 * r ≤ n →
      ∃ E E' : Finset (Finset (Fin n)), (∀ e ∈ E, e.card = r) ∧ (∀ e ∈ E', e.card = r) ∧
        (∀ A : Finset (Fin n), A.card = 1 →
          (E.filter (fun e => A ⊆ e)).card = (E'.filter (fun e => A ⊆ e)).card) ∧
        crisp E 2 ≠ crisp E' 2 := by sorry

end HypRecov
