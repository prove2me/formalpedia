-- Prove2me | Theorems.Thm_LovaszECCKernel_claim_12
-- name    : LovaszECCKernel.claim_12
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T16:56:59.896306+00:00
-- url     : https://prove2.me/theorems/407c0692-3df9-441a-83e4-aaa6653d8c58
-- title:
--   Claim 12 — if Algorithm 1 reaches Line 11 then $m\ge n(n-3)/6$
-- statement:
--   **Claim 12.** Let $G$ be a finite simple graph with $n$ vertices and $m$ edges, and $k\ge0$. If Algorithm 1 reaches Line 11, i.e. neither Line 2 (`if` $m\le\mathrm{Lb}(G)-k$ `then return` $\mathcal Y$) nor Line 5 (`if` $k\ge m$ `and` $k\ge n$ `then return` $(G,k)$) returned, then
--   $$m\ \ge\ \frac{n(n-3)}{6}.$$
--
--   So after preprocessing the graph is dense, $m=\Theta(n^2)$, and the $O(n^2)$ Cluster Editing approximation runs in time $O(n+m)$.
--
--   Differences from the source:
--   - reading: A reaches Line 11 → ¬(m ≤ Lb(G) − k) and ¬(k ≥ m ∧ k ≥ n) for the input graph G; reason: Lines 2 and 5 are the only returns before Line 11, and the proof of the claim uses exactly these two tests on the input's n and m
--   - encoding: m ≥ n·(n − 3)/6 → compared in ℝ, the test of Line 2 in ℤ; reason: no truncated subtraction or division
-- source:
--   Fomin, Golovach, Khargeliia, Sagunov, Simonov, Stability Meets Kernelization: Algorithmic Extensions of the Lovász and Erdős–Goodman–Pósa Theorems, STOC 2027 submission (manuscript sha256 a9d53ab8…), Claim 12 and Algorithm 1, p.42 (= PDF p.42)

import Mathlib
import Definitions.Def_LovaszECCKernel_nonEdges
import Definitions.Def_LovaszECCKernel_Lb

set_option autoImplicit false

namespace LovaszECCKernel

/-- **Claim 12** (Fomin, Golovach, Khargeliia, Sagunov, Simonov, *Stability Meets Kernelization: Algorithmic
Extensions of the Lovász and Erdős–Goodman–Pósa Theorems*, STOC 2027 submission (manuscript
sha256 a9d53ab8…), Claim 12, p.42 (= PDF p.42)): "If A reaches Line 11, then
m ≥ n · (n − 3)/6." Algorithm 1 (p.42) reaches Line 11 when neither Line 2 ("if m ≤ Lb(G) − k then
return Y") nor Line 5 ("if k ≥ m and k ≥ n then return (G, k)") returned.

**Formalization Note** `n` and `m` are the vertex and edge counts of the input graph `G`, the graph
tested in Lines 2 and 5 (the proof of the claim uses exactly these two tests). The test of Line 2 is
compared in `ℤ`; the conclusion in `ℝ`. -/
theorem claim_12 {V : Type*} [Fintype V] (G : SimpleGraph V) (k : ℕ)
    (h₂ : ¬ ((edgeCount G : ℤ) ≤ (Lb G : ℤ) - k))
    (h₅ : ¬ (edgeCount G ≤ k ∧ Fintype.card V ≤ k)) :
    (Fintype.card V : ℝ) * ((Fintype.card V : ℝ) - 3) / 6 ≤ edgeCount G := by sorry

end LovaszECCKernel
