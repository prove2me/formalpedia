-- Prove2me | Theorems.Thm_GGHRSW_ColoredMatrix_theorem_6_collision_bound
-- name    : GGHRSW.ColoredMatrix.theorem_6_collision_bound
-- status  : Proved
-- author  : @Victorized
-- created : 2026-11-03T03:24:57.065047+00:00
-- url     : https://prove2.me/theorems/2cab2f1c-745a-4663-aef0-8ce016b588f1
-- title:
--   Proof of Theorem 6, §C.3.1, pp. 41–43 — formal expressions that are not identically equal collide with probability $O((n+1)/p)$
-- statement:
--   Let $p$ be a prime, $BP$ a branching program of length $n$ over $\ell$ input bits, and $(J,\sigma)$ a partial assignment. Let $e,e'$ be two formal query expressions over the handles of $DB(p,BP,(J,\sigma))$ that have the same shape (same dimensions and colours) and are **not** identically equal, i.e. their values differ for at least one sample of $\mathcal{RND}_p(BP)$. Then
--   $$\Pr_{\omega\leftarrow\mathcal{RND}_p(BP)}\big[e(\omega)=e'(\omega)\big]\;\le\;\frac{C\,(n+1)}{p},$$
--   where $C$ is an absolute constant, independent of $p$, $BP$, $(J,\sigma)$, $e$ and $e'$.
--
--   This is the per-query estimate of the proof of Theorem 6 (§C.3.1). In every colour case, partial evaluations with $LC=i>0$ or $RC=j<n+2$ as well as full evaluations from colour $0$ to colour $n+2$, a new matrix coincides with an earlier one only with probability $O(n/p)$, unless the two expressions agree for every sample. Summed over the at most $T^2$ pairs of handles of an execution, this gives the $O(nT^2/p)$ of Theorem 6.
--
--   **Formalization Note.** Expressions, shapes, values and identical equality are those of `Definitions.Def_GGHRSW_ColoredMatrix_Simulator`. The probability is over the uniform sample of the finite sample space. The bound is written with $n+1$ so that it also covers programs with no steps, where only the bookend vectors are available. The constant is quantified first.
--
--   **Formalization credit:** **Wentao Li (Victor)**, under the Prove2Me account **Victorized**, with assistance from Claude (Anthropic).
-- source:
--   Garg, Gentry, Halevi, Raykova, Sahai and Waters, Candidate Indistinguishability Obfuscation and Functional Encryption for All Circuits, SIAM J. Comput. 45(3), 2016 (authors' version of July 21, 2013), App. C.3.1, proof of Theorem 6, pp. 41–43 (the per-query collision bounds)

import Mathlib
import Definitions.Def_GGHRSW_ColoredMatrix_Model
import Definitions.Def_GGHRSW_ColoredMatrix_Simulator

namespace GGHRSW.ColoredMatrix

open Classical in
theorem theorem_6_collision_bound : ∃ C : ℝ, ∀ (p : ℕ) [Fact p.Prime] (bp : BP)
    (J : Finset (Fin bp.ℓ)) (σ : Fin bp.ℓ → Bool) (e e' : QExpr p) (s : Shape),
    e.shape bp J = some s → e'.shape bp J = some s → ¬ IdenticallyEqual bp J σ e e' →
      ((Finset.univ.filter fun ω : Sample p bp =>
          e.eval (initDB bp J σ ω) = e'.eval (initDB bp J σ ω)).card : ℝ) /
        Fintype.card (Sample p bp) ≤ C * (bp.n + 1) / p := by sorry

end GGHRSW.ColoredMatrix
