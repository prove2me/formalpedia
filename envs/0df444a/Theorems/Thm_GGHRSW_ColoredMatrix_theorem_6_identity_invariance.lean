-- Prove2me | Theorems.Thm_GGHRSW_ColoredMatrix_theorem_6_identity_invariance
-- name    : GGHRSW.ColoredMatrix.theorem_6_identity_invariance
-- status  : Proved
-- author  : @Victorized
-- created : 2026-11-03T03:25:12.106004+00:00
-- url     : https://prove2.me/theorems/39b5bf7c-1869-404c-b7ff-b2fd68313117
-- title:
--   Proof of Theorem 6, App. C.3 — for $p > C(n+1)$, functionally equivalent assignments have the same identically-equal expressions
-- statement:
--   Let $p$ be a prime, $BP$ a branching program of length $n$ over $\ell$ input bits, and let $(J,\sigma)$ and $(J,\sigma')$ be functionally equivalent partial assignments, $F|_\sigma=F|_{\sigma'}$. There is an absolute constant $C$ such that, whenever $p>C(n+1)$, for any two formal query expressions $e,e'$ of the same shape,
--   $$e\equiv_\sigma e'\iff e\equiv_{\sigma'} e',$$
--   where $e\equiv_\sigma e'$ means that the values of $e$ and $e'$ for the database $DB(p,BP,(J,\sigma))$ agree for every sample of $\mathcal{RND}_p(BP)$.
--
--   In words: which pairs of formal expressions are identically equal depends on the assignment only through the restricted function $F|_\sigma$. This is the statement that the simulator in the proof of Theorem 6 can answer every equality query of the adversary with access to $F|_\sigma$ alone, so that its output is the same for functionally equivalent assignments.
--
--   **Formalization Note.** Expressions, shapes and identical equality are those of `Definitions.Def_GGHRSW_ColoredMatrix_Simulator`; an expression refers to handles, so the same expression denotes the matrices of $\sigma$ in one database and of $\sigma'$ in the other. The hypothesis $p>C(n+1)$ excludes small fields, where a nonzero polynomial expression in the random entries may vanish as a function on $\mathbb Z_p$; for those $p$ the bound of Theorem 6 exceeds $1$ and nothing needs to be simulated.
--
--   **Formalization credit:** **Wentao Li (Victor)**, under the Prove2Me account **Victorized**, with assistance from Claude (Anthropic).
-- source:
--   Garg, Gentry, Halevi, Raykova, Sahai and Waters, Candidate Indistinguishability Obfuscation and Functional Encryption for All Circuits, SIAM J. Comput. 45(3), 2016 (authors' version of July 21, 2013), App. C.3, proof of Theorem 6, pp. 38–43 (the simulator answers equality queries using F|σ only)

import Mathlib
import Definitions.Def_GGHRSW_ColoredMatrix_Model
import Definitions.Def_GGHRSW_ColoredMatrix_Simulator

namespace GGHRSW.ColoredMatrix

theorem theorem_6_identity_invariance : ∃ C : ℕ, ∀ (p : ℕ) [Fact p.Prime] (bp : BP)
    (J : Finset (Fin bp.ℓ)) (σ σ' : Fin bp.ℓ → Bool), FunctionallyEquivalent bp J σ σ' →
    C * (bp.n + 1) < p → ∀ (e e' : QExpr p) (s : Shape),
      e.shape bp J = some s → e'.shape bp J = some s →
      (IdenticallyEqual bp J σ e e' ↔ IdenticallyEqual bp J σ' e e') := by sorry

end GGHRSW.ColoredMatrix
