-- Prove2me | Theorems.Thm_OptQJunta_fact_4_4
-- name    : OptQJunta.fact_4_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T20:21:32.849557+00:00
-- url     : https://prove2.me/theorems/697e42bd-7b40-4c07-9be2-a4e0b38a13d9
-- title:
--   Fact 4.4 — edge-isoperimetric inequality $|\partial B|\ge|B|\log(2^h/|B|)$
-- statement:
--   Let $h\ge1$ be an integer and let $\varnothing\neq B\subseteq\{0,1\}^h$ satisfy $|B|\le2^{h-1}$. Let $\partial B$ be the set of unordered hypercube edges with one endpoint in $B$ and the other outside $B$. Then
--
--   $$
--   |\partial B|\ \ge\ |B|\,\log_2\frac{2^h}{|B|}.
--   $$
--
--   It bounds the number of address coordinates a junta must keep in the analysis of partial support recovery.
--
--   **Formalization Note** $|\partial B|$ is counted as the number of pairs $(x,i)$ with $x\in B$ and $x\oplus e_i\notin B$.
--
--   Differences from the source:
--   - encoding: $|\partial B|$, the number of unordered boundary edges → the number of pairs $(x,i)$ with $x\in B$, $x\oplus e_i\notin B$; reason: each boundary edge has exactly one endpoint in $B$, so the two counts agree
--   - encoding: bits $\{0,1\}$, coordinates $[n]=\{1,\dots,n\}$ → bits `Bool` (`QAlgorithms.Qubits n = Fin n → Bool`), coordinates `Fin n` from $0$; reason: a relabelling; same instances
-- source:
--   Bao, Gao, Yao, Optimal Quantum Junta Testing, preprint (version of November 3, 2026, sha256 a97d09a4…), Fact 4.4, p.56

import Mathlib
import Definitions.Def_OptQJunta_infl

open QAlgorithms

namespace OptQJunta

/-- **Fact 4.4** (Edge-isoperimetric inequality [O'D14, Theorem 2.39]; Bao, Gao, Yao, *Optimal Quantum Junta Testing*, preprint, version of November 3, 2026, sha256 a97d09a4…, p.56). Let `h ≥ 1` be
an integer and let `∅ ≠ B ⊆ {0,1}^h` satisfy `|B| ≤ 2^{h−1}`. Let `∂B` be the set of unordered
hypercube edges with one endpoint in `B` and the other outside `B`. Then
`|∂B| ≥ |B| log(2^h/|B|)`.

**Formalization Note** `log` is base two. `|∂B|` is counted as the number of pairs `(x, i)` with
`x ∈ B` and `x ⊕ e_i ∉ B`; each boundary edge has exactly one endpoint in `B`, so this is a bijection
with `∂B`. -/
theorem fact_4_4 (h : ℕ) (hh : 1 ≤ h) (B : Finset (Qubits h)) (hB : B.Nonempty)
    (hcard : B.card ≤ 2 ^ (h - 1)) :
    (B.card : ℝ) * Real.logb 2 ((2 : ℝ) ^ h / B.card) ≤
      (((B ×ˢ (Finset.univ : Finset (Fin h))).filter fun p => flipAt p.1 p.2 ∉ B).card : ℝ) := by sorry

end OptQJunta
