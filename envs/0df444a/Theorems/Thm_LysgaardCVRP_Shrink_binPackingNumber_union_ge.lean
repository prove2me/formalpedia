-- Prove2me | Theorems.Thm_LysgaardCVRP_Shrink_binPackingNumber_union_ge
-- name    : LysgaardCVRP.Shrink.binPackingNumber_union_ge
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-28T16:47:34.101353+00:00
-- url     : https://prove2.me/theorems/bbdf7ec5-096d-4a5d-bc51-6b2aaa236ba0
-- title:
--   Monotonicity of the bin-packing number: $2r(S \cup T) - 2r(T) \ge 0$
-- statement:
--   Let $Q > 0$ be the vehicle capacity and let every customer $i$ have an integer demand with $0 < q_i \le Q$. For any two sets $S, T$ of customers, with $r$ the bin-packing number,
--
--   $$2r(S \cup T) - 2r(T) \ge 0 .$$
--
--   This is the step of the proof of Proposition 1 that compares the right-hand sides of the capacity inequalities on $T$ and on $S \cup T$.
--
--   **Formalization Note** The hypothesis $q_i \le Q$ makes $r$ a genuine minimum; the positivity of demands and capacity are the paper's standing assumptions.
-- source:
--   Lysgaard, Letchford & Eglese, A new branch-and-cut algorithm for the capacitated vehicle routing problem, Math. Program. Ser. A 100 (2004), p. 426 (PDF p. 4), proof of Proposition 1

import Mathlib
import Definitions.Def_LysgaardCVRP_Shrink_binPackingNumber

namespace LysgaardCVRP.Shrink

/-- Monotonicity of the bin-packing number, in the form used in the proof of Proposition 1 of
Lysgaard, Letchford & Eglese, *A new branch-and-cut algorithm for the capacitated vehicle
routing problem*, Math. Program. Ser. A 100 (2004), p. 426 (PDF p. 4) (unnumbered): "It is trivially true that
$2r(S\cup T) - 2r(T) \ge 0$".

**Formalization Note.** Stated for customer sets `S`, `T` (not containing the depot `0`) under
the paper's standing hypotheses $Q > 0$ and $0 < q_i \le Q$ for every customer (§1, p. 423); the
hypothesis $q_i \le Q$ is what makes `binPackingNumber` a genuine minimum rather than the junk
value `sInf ∅ = 0`. -/
theorem binPackingNumber_union_ge {n : ℕ} (q : Fin (n + 1) → ℕ) (Q : ℝ) (hQ : 0 < Q)
    (hq : ∀ i : Fin (n + 1), i ≠ 0 → 0 < q i ∧ (q i : ℝ) ≤ Q)
    (S T : Finset (Fin (n + 1))) (hS0 : (0 : Fin (n + 1)) ∉ S) (hT0 : (0 : Fin (n + 1)) ∉ T) :
    0 ≤ 2 * (binPackingNumber q Q (S ∪ T) : ℝ) - 2 * (binPackingNumber q Q T : ℝ) := by sorry

end LysgaardCVRP.Shrink
