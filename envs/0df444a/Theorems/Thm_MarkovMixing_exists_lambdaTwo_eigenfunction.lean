-- Prove2me | Theorems.Thm_MarkovMixing_exists_lambdaTwo_eigenfunction
-- name    : MarkovMixing.exists_lambdaTwo_eigenfunction
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-27T01:08:10.666547+00:00
-- url     : https://prove2.me/theorems/01f44538-8646-4a44-bef9-7fd0b2aa45f0
-- title:
--   An eigenfunction attaining $λ_2$, normalized and orthogonal to the constants
-- statement:
--   Let $P$ be an irreducible stochastic matrix on a finite state space $V$ with at least two
--   states, reversible with respect to its stationary distribution $\pi$ (detailed balance). Let
--   $\lambda_2$ denote the second largest eigenvalue of $P$. Then $\lambda_2$ is attained by an
--   eigenfunction that is normalized and has mean zero: there exists $g : V \to \mathbb{R}$ with
--
--   1. $\langle g, g \rangle_{\pi} = 1$;
--   2. $\mathbb E_{\pi}[g] = 0$, that is $\sum_x \pi(x) g(x) = 0$;
--   3. $P g = \lambda_2\, g$.
--
--   The two normalizations are what make the eigenfunction usable. Mean zero places $g$ in the
--   orthogonal complement of the constant eigenfunction belonging to the eigenvalue $1$, and unit
--   norm makes it a feasible point of the variational problem for the spectral gap. Consequently
--   $\lambda_2$ is not merely a supremum but a value attained, which is what allows a lower bound on
--   the gap proved for all test functions to be turned into an upper bound by evaluating at $g$ —
--   the direction needed for Cheeger-type inequalities.
-- source:
--   D. A. Levin, Y. Peres and E. L. Wilmer, Markov Chains and Mixing Times, 2nd ed., AMS 2017, Lemma 12.2 and §12.2; carved from the accepted proof of DiaconisStroock.CanonPaths.proposition_7, https://prove2.me/submissions/cbb05a5c-f0c1-49a4-815e-fb54ebb129bc

import Mathlib
import Definitions.Def_mm_spectral

set_option autoImplicit false
open scoped BigOperators
open MarkovMixing

theorem MarkovMixing.exists_lambdaTwo_eigenfunction {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]
    (hV : 2 ≤ Fintype.card V) (P : Matrix V V ℝ) (hP : MarkovMixing.IsStochastic P)
    (hirr : MarkovMixing.Irreducible P)
    (π : V → ℝ) (hπ : MarkovMixing.IsStationary P π)
    (hrev : MarkovMixing.DetailedBalance P π) :
    ∃ g : V → ℝ, MarkovMixing.innerPi π g g = 1 ∧ MarkovMixing.distExp π g = 0 ∧
      P.mulVec g = (MarkovMixing.lambdaTwo P) • g := by sorry
