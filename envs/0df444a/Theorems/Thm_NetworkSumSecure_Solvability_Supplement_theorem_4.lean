-- Prove2me | Theorems.Thm_NetworkSumSecure_Solvability_Supplement_theorem_4
-- name    : NetworkSumSecure.Solvability.Supplement.theorem_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T07:10:08.43664+00:00
-- url     : https://prove2.me/theorems/fad9ab9d-ff6f-41f9-8ce2-0577552d69c1
-- title:
--   Theorem 4 — exact minimum total private randomness
-- statement:
--   Let $N$ be the published finite directed acyclic multigraph network and let $r\in\mathbb N$. Assume the family $\Pi$ of edge-disjoint $(r+1)$-path systems from the users to the server is nonempty. For $Q\in\Pi$, let $S_Q$ be the set of users starting at least one path of $Q$. There is a system $Q_{\max}\in\Pi$ attaining
--
--   $$
--   M=|S_{Q_{\max}}|=\max_{Q\in\Pi}|S_Q|.
--   $$
--
--   Over every finite field $F$, every feasible scalar linear scheme with any private-key assignment $z:U\to\mathbb N$ satisfies the universal lower bound
--
--   $$
--   r+1-M\ \le\ \sum_{i\in U}z_i.
--   $$
--
--   For every finite field with $|F|\ge s+|\mathcal W_r|+1$, where $s=|U|$ and $\mathcal W_r=\{W\subseteq E:|W|\le r\}$, there exist an assignment $z$, a causal local code with this assignment, and a linear decoder giving a feasible scheme and attaining equality. Thus the minimum over all assignments, codes and decoders exists and equals
--
--   $$
--   C^*_{\mathrm{rnd}}=r+1-\max_{Q\in\Pi}|S_Q|.
--   $$
--
--   This companion theorem determines the optimum total randomness rather than merely a lower bound or infimum. Its proof uses Theorem 2, already included in this supplement, and brings no additional supporting result.
--
--   **Formalization Note** The maximizing system is chosen before quantifying over finite fields. The total randomness is the ordinary finite sum of the key counts in Definition 2. Cardinalities and sums are cast into $\mathbb Z$ for subtraction; each starting user is the image of some one of the $r+1$ path indices, so $M\le r+1$. No convention assigns a spurious value to an empty minimum.
--
--   Differences from the source:
--   - reading: the maximum over Π and the minimum over feasible schemes are written without an explicit nonemptiness clause → HasPaths N (r+1), equivalently Π is nonempty; reason: this is the domain on which the printed maximum and minimum are defined; the proof explicitly selects Q*∈Π
--   - reading: a sufficiently large field, without an explicit uniform threshold in the theorem sentence → every finite field F with fieldThreshold r = s + |W_r| + 1 ≤ |F| in the existence direction; reason: this is the published goal convention; (34) and (53) give a witness independent of key assignment, code, field characteristic, and path choice
--   - generalization: the standing convention assumes a sufficiently large finite field → the necessary conclusion also holds over every finite field without a cardinality hypothesis; reason: the necessity proof uses only correctness, exact sum-security, and finite-dimensional linear algebra; it does not use either field-size estimate (34) or (53)
--   - encoding: C*_rnd = r+1 − max over Q∈Π of |S_Q| → an actual maximizing path system Qmax, a universal lower bound on total keys, and a feasible scheme attaining r+1−|S_Qmax|; subtraction in ℤ; reason: attainment plus the universal bound expresses the full minimum, and an explicit maximum avoids empty or unbounded supremum defaults; integer subtraction preserves the exact formula
--   - encoding: users indexed by 1 ≤ i ≤ s and sets of r+1 paths → arbitrary finite user types and indexed families Fin (r+1) → UserPath N with EdgeDisjoint; reason: finite relabeling changes no instance; nonempty edge-disjoint paths cannot repeat, and common vertices remain allowed
-- source:
--   Yang Bai, Xuan Guang, Lizhi Wang, STOC 2027 submission #1291 (October 2026), p. 11, Theorem 4 (PDF p. 13). Formula (15), proof pp. 11–12 (PDF pp. 13–14), Definition 2 and (8), p. 9 (PDF p. 11).

import Mathlib
import Definitions.Def_NetworkSumSecure_Solvability_encoding
import Definitions.Def_NetworkSumSecure_Solvability_Supplement_path_starts

open scoped BigOperators

namespace NetworkSumSecure.Solvability.Supplement

/-- Theorem 4, printed p.11 (PDF 13), proof pp.11–12 (PDF 13–14).
The path family is nonempty, as required by the printed max/min formula.
An actual maximizer and an attained minimum replace the two extremum symbols.
Subtraction is in Z, so no natural-number truncation is implicit. -/
theorem theorem_4 {V E U : Type} [Fintype V] [Fintype E] [Fintype U]
    (N : Network V E U) (r : ℕ) (hpaths : HasPaths N (r + 1)) :
    ∃ Qmax : Fin (r + 1) → UserPath N,
      EdgeDisjoint Qmax ∧
      (∀ Q : Fin (r + 1) → UserPath N, EdgeDisjoint Q →
        (startSet Q).card ≤ (startSet Qmax).card) ∧
      (∀ (F : Type) [Field F] [Fintype F],
        ∀ (z : U → ℕ) (C : LocalCode N F z) (φ : Decoder N F),
          Feasible C φ r →
            (r + 1 : ℤ) - ((startSet Qmax).card : ℤ) ≤ ∑ i, (z i : ℤ)) ∧
      (∀ (F : Type) [Field F] [Fintype F],
        fieldThreshold (E := E) (U := U) r ≤ Fintype.card F →
          ∃ (z : U → ℕ) (C : LocalCode N F z) (φ : Decoder N F),
            Feasible C φ r ∧
              (∑ i, (z i : ℤ)) = (r + 1 : ℤ) - ((startSet Qmax).card : ℤ)) := by sorry

end NetworkSumSecure.Solvability.Supplement
