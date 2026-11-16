-- Prove2me | Theorems.Thm_NetworkSumSecure_Solvability_Supplement_theorem_2
-- name    : NetworkSumSecure.Solvability.Supplement.theorem_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T07:09:20.877324+00:00
-- url     : https://prove2.me/theorems/8af3ae9f-2466-41db-a49d-9890fe4916c7
-- title:
--   Theorem 2 — feasible private-key assignments
-- statement:
--   Let $N$ be the published finite directed acyclic multigraph network with user set $U$, let $r\in\mathbb N$ be the security level, and fix a private-key assignment $z:U\to\mathbb N$. Write $\mathcal E_F(z)$ for existence, over a finite field $F$, of a scalar linear causal local code and a linear server decoder that are feasible with exactly this assignment $z$. For $Q=(Q_1,\ldots,Q_{r+1})$, let $a_i(Q)$ count its paths starting at user $i$. Define the path condition
--
--   $$
--   \mathcal P(z):\quad \exists Q,\quad Q\text{ consists of }r+1\text{ edge-disjoint user-to-server paths},
--   \qquad a_i(Q)\le 1+z_i\quad\text{for every }i\in U.
--   $$
--
--   For every finite field $F$, necessity holds: $\mathcal E_F(z)\Rightarrow\mathcal P(z)$. With $s=|U|$ and $\mathcal W_r=\{W\subseteq E:|W|\le r\}$, the full characterization holds for every finite field with $|F|\ge s+|\mathcal W_r|+1$:
--
--   $$
--   \mathcal E_F(z)\quad\Longleftrightarrow\quad\mathcal P(z).
--   $$
--
--   This companion theorem determines all admissible distributions of private randomness among the users. Its supporting result in this supplement is Lemma 7. The published Theorem 6 and Algorithm 1 supply its construction ingredients; they remain base items.
--
--   **Formalization Note** Both code and decoder are existentially chosen for `LocalCode N F z`; the assignment is neither enlarged nor replaced by a smaller one. The path-count constraint applies also to users with no selected path. The finite-field threshold is fixed before the field and is independent of $z$.
--
--   Differences from the source:
--   - reading: a sufficiently large field, without an explicit uniform threshold in the theorem sentence → every finite field F with fieldThreshold r = s + |W_r| + 1 ≤ |F| in the existence direction; reason: this is the published goal convention; (34) and (53) give a witness independent of key assignment, code, field characteristic, and path choice
--   - generalization: the standing convention assumes a sufficiently large finite field → the necessary conclusion also holds over every finite field without a cardinality hypothesis; reason: the necessity proof uses only correctness, exact sum-security, and finite-dimensional linear algebra; it does not use either field-size estimate (34) or (53)
--   - encoding: users indexed by 1 ≤ i ≤ s and sets of r+1 paths → arbitrary finite user types and indexed families Fin (r+1) → UserPath N with EdgeDisjoint; reason: finite relabeling changes no instance; nonempty edge-disjoint paths cannot repeat, and common vertices remain allowed
-- source:
--   Yang Bai, Xuan Guang, Lizhi Wang, STOC 2027 submission #1291 (October 2026), p. 10, Theorem 2 (PDF p. 12). Proof §5, pp. 18–19 (PDF pp. 20–21); field bounds (34), p. 16 (PDF p. 18), and (53), p. 23 (PDF p. 25).

import Mathlib
import Definitions.Def_NetworkSumSecure_Solvability_algorithm

namespace NetworkSumSecure.Solvability.Supplement

/-- Theorem 2, printed p.10 (PDF 12), proof pp.18–19 (PDF 20–21).
The key assignment is fixed exactly. Necessity holds over every finite field;
the uniform field-size witness for sufficiency is independent of z. -/
theorem theorem_2 {V E U : Type} [Fintype V] [Fintype E] [Fintype U]
    (N : Network V E U) (r : ℕ) (z : U → ℕ) :
    (∀ (F : Type) [Field F] [Fintype F],
      (∃ (C : LocalCode N F z) (φ : Decoder N F), Feasible C φ r) →
        ∃ Q : Fin (r + 1) → UserPath N,
          EdgeDisjoint Q ∧ ∀ i, pathCount Q i ≤ 1 + z i) ∧
    (∀ (F : Type) [Field F] [Fintype F],
      fieldThreshold (E := E) (U := U) r ≤ Fintype.card F →
        ((∃ (C : LocalCode N F z) (φ : Decoder N F), Feasible C φ r) ↔
          ∃ Q : Fin (r + 1) → UserPath N,
            EdgeDisjoint Q ∧ ∀ i, pathCount Q i ≤ 1 + z i)) := by sorry

end NetworkSumSecure.Solvability.Supplement
