-- Prove2me | Theorems.Thm_InvariantSDP_BlockDiag_blockRel_equivalence
-- name    : InvariantSDP.BlockDiag.blockRel_equivalence
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-21T13:39:30.131544+00:00
-- url     : https://prove2.me/theorems/60030722-e3f3-41a6-97f0-8efced41c2c3
-- title:
--   Proof of Theorem 2.7, p. 14 — $i\sim j \iff I_i\mathcal A I_j\neq\{0\}$ is an equivalence relation
-- statement:
--   Let $\mathcal A \subseteq \mathbb C^{n\times n}$ be a matrix ∗-algebra and let $\mathcal B$ be an inclusionwise maximal commutative ∗-subalgebra of $\mathcal A$ in diagonal form $\mathcal B = \mathbb C I_1 + \dots + \mathbb C I_k$ for a partition $[n] = S_0 \cup S_1 \cup \dots \cup S_k$ with $S_1, \dots, S_k$ nonempty. Define the relation $\sim$ on $\{1, \dots, k\}$ by
--   $$i \sim j \iff I_i \mathcal A I_j \neq \{0\},$$
--   i.e. there is $X \in \mathcal A$ with $I_i X I_j \neq 0$. Then $\sim$ is an equivalence relation.
--
--   Its classes group the diagonal blocks into the simple components of $\mathcal A$: summing $I_j$ over a class gives the minimal idempotents $E_1, \dots, E_d$ of the center.
--
--   **Formalization Note** Indices are 0-based (`Fin k` for $\{1,\dots,k\}$). The setting is the same as for observations (i)–(iii).
-- source:
--   Bachoc, Gijswijt, Schrijver & Vallentin, Invariant semidefinite programs, arXiv:1007.2905v2, p. 14, proof of Theorem 2.7

import Mathlib
import Definitions.Def_InvariantSDP_BlockDiag_Basic

namespace InvariantSDP.BlockDiag

/-- Proof of Theorem 2.7, p. 14: in the setting of observations (i)–(iii), the relation `i ∼ j` iff
`I_i 𝒜 I_j ≠ {0}` is an equivalence relation on `{1, …, k}`. -/
theorem blockRel_equivalence {n k : ℕ} (A B : NonUnitalStarSubalgebra ℂ (Matrix (Fin n) (Fin n) ℂ))
    (S : Fin n → Option (Fin k)) (hB : IsMaxCommutative A B) (hS : IsDiagForm B S) :
    Equivalence (blockRel A S) := by sorry

end InvariantSDP.BlockDiag
