-- Prove2me | Theorems.Thm_MarkovMixing_eigenvalue_basic
-- name    : MarkovMixing.eigenvalue_basic
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-08-21T21:45:34.37771+00:00
-- url     : https://prove2.me/theorems/60a51760-d84a-4761-86fd-85ba51cca426
-- title:
--   Lemma 12.1 -- basic spectral facts for stochastic matrices
-- statement:
--   Let $P$ be a stochastic matrix on a finite state space $V$ (nonnegative entries, rows summing to one). A real number $\lambda$ is an **eigenvalue** of $P$ when there is a nonzero function $f:V\to\mathbb R$ — an **eigenfunction** — with $Pf=\lambda f$, where $(Pf)(x)=\sum_yP(x,y)f(y)$. Recall that $P$ is **irreducible** when every state can reach every other in some number of steps, and **aperiodic** when the return times to each state have greatest common divisor one.
--
--   The theorem (Lemma 12.1 of Levin–Peres–Wilmer) asserts:
--
--   1. every eigenvalue of $P$ satisfies $|\lambda|\le1$;
--   2. if $P$ is irreducible, every function with $Pf=f$ is constant — the eigenspace of the eigenvalue $1$ is one-dimensional;
--   3. if $P$ is irreducible and aperiodic, then $-1$ is **not** an eigenvalue of $P$.
--
--   These are the basic facts that position the spectrum inside $[-1,1]$ with $1$ a simple eigenvalue and $-1$ excluded, so that the spectral gap of an irreducible aperiodic chain is genuinely positive — the starting point of the spectral theory of Chapters 12–13.
-- source:
--   D. A. Levin, Y. Peres, E. L. Wilmer, Markov Chains and Mixing Times, AMS 2009, https://documents.epfl.ch/groups/i/ip/ipg/www/2013-2014/Random_Walks/markovmixing.pdf, Section 12.1, Lemma 12.1, p. 153

import Definitions.Def_mm_spectral

namespace MarkovMixing

/-- **Lemma 12.1** (LPW): (i) every eigenvalue of a transition matrix has
`|λ| ≤ 1`; (ii) for an irreducible chain the eigenfunctions of eigenvalue `1`
are the constants; (iii) an irreducible aperiodic chain does not have `−1`
as an eigenvalue. -/
theorem eigenvalue_basic {V : Type*} [Fintype V] [DecidableEq V]
    (P : Matrix V V ℝ) (hP : IsStochastic P) :
    (∀ lam : ℝ, IsEigenvalue P lam → |lam| ≤ 1) ∧
    (Irreducible P → ∀ f : V → ℝ, P.mulVec f = f → ∀ x y : V, f x = f y) ∧
    (Irreducible P → Aperiodic P → ¬IsEigenvalue P (-1)) := by
  sorry

end MarkovMixing
