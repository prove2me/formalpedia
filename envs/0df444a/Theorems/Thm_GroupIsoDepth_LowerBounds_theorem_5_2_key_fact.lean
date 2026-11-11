-- Prove2me | Theorems.Thm_GroupIsoDepth_LowerBounds_theorem_5_2_key_fact
-- name    : GroupIsoDepth.LowerBounds.theorem_5_2_key_fact
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T16:41:17.66451+00:00
-- url     : https://prove2.me/theorems/f7bbcf47-982a-481a-b27f-f694183aa8e1
-- title:
--   Theorem 5.2, proof (key fact) — no two quasigroup tables differ in exactly one entry, hence not in exactly one bit
-- statement:
--   Let $n\in\mathbb N$.
--   1. If $T$ and $T'$ are Latin squares of order $n$ (multiplication tables of quasigroups) and $T(a,b)=T'(a,b)$ for every $(a,b)\ne(i,j)$, then also $T(i,j)=T'(i,j)$: two quasigroup tables never differ in exactly one entry.
--   2. A fortiori, if two bit strings $x,x'$ of length $N=n^2\lceil\log_2 n\rceil$ both encode Latin squares and agree on every bit except possibly $v$, then they agree on $v$.
--
--   (The reason: removing one entry of a row of a Latin square leaves its value determined as the only label missing from the rest of the row.) Group tables are Latin squares, so the statement covers groups.
--
--   Differences from the source:
--   - reading: there are no two multiplication tables of quasigroups that differ in only one entry, hence ... only one bit → two Latin squares that agree off one entry agree everywhere; two bit-tables that are both Latin squares and agree off one bit agree everywhere; reason: 'differ in exactly one entry/bit' negated as 'agree off it implies agree on it'
--   - encoding: each entry a ⌈log₂ n⌉-bit label of an element of [n] (bit order not fixed) → TableVar n = Fin n × Fin n × Fin (Nat.clog 2 n); entry = Σ_b x(i,j,b)·2^b (bit b has weight 2^b); labels [n] = Fin n = {0,…,n−1}; reason: any fixed bit order and label set is a renaming of the input variables; no instance and no size changes
-- source:
--   Grochow, Kardeş, Levet, Group Isomorphism: Depth-2½ Circuits and Lower Bounds, STOC 2027 submission (manuscript sha256 cd6cacd4…), proof of Theorem 5.2 (p. 36, PDF 37)

import Mathlib
import Definitions.Def_GroupIsoDepth_LowerBounds_CayleyTables

namespace GroupIsoDepth.LowerBounds

/-- Proof of Theorem 5.2, key fact (printed p. 36, PDF 37): no two multiplication tables of
quasigroups (Latin squares) differ in exactly one entry, hence a fortiori they cannot differ in
exactly one bit. (1) Two Latin squares on `[n]` that agree off the entry `(i, j)` agree at `(i, j)`.
(2) Two bit-tables of order `n` that are both Latin squares and agree off one input bit `v` agree
at `v`. -/
theorem theorem_5_2_key_fact (n : ℕ) :
    (∀ T T' : Fin n → Fin n → ℕ, IsLatinSquare T → IsLatinSquare T' →
      ∀ i j : Fin n, (∀ a b : Fin n, (a, b) ≠ (i, j) → T a b = T' a b) → T i j = T' i j) ∧
    (∀ x x' : TableVar n → Bool, LatinSq n x → LatinSq n x' →
      ∀ v : TableVar n, (∀ w : TableVar n, w ≠ v → x w = x' w) → x v = x' v) := by sorry

end GroupIsoDepth.LowerBounds
