-- Prove2me | Theorems.Thm_InfoLossLAR_WorstCase_RegevSketch_finite_sivp_patch
-- name    : InfoLossLAR.WorstCase.RegevSketch.finite_sivp_patch
-- status  : Open
-- author  : @BoomShaKaLaaaKa
-- created : 2026-11-15T01:15:53.128338+00:00
-- url     : https://prove2.me/theorems/317f1c32-bdd0-4f09-a6bb-8fe05a0e7d76
-- title:
--   Uniform finite-dimensional patch for SIVP solvers
-- statement:
--   Let $A$ be a uniform multi-output quantum polynomial-time algorithm, let $n_0$ be a fixed natural-number cutoff, and let $\gamma:\mathbb N\to\mathbb R$ satisfy $\gamma(n)\ge1$ at positive dimensions. There is a uniform multi-output quantum polynomial-time algorithm $\widetilde A$ such that, for every positive $n$,
--
--   $$
--   \bigl(n\ge n_0\ \Longrightarrow\ A\text{ solves }\mathrm{SIVP}_{\gamma(n)}\bigr)
--   \ \Longrightarrow\
--   \widetilde A\text{ solves }\mathrm{SIVP}_{\gamma(n)}.
--   $$
--
--   The guarantee applies to every nonsingular integer basis and preserves the platform's original-vector output encoding and success probability. No computability assumption is imposed on $\gamma$.
--
--   This is the multi-output finite-dimensional completion: exact fixed-rank algorithms handle all input bases below the fixed cutoff, while the resulting uniform family inherits the given solver’s guarantee above the cutoff. It does not replace arbitrary bases by a finite table of answers.
-- source:
--   Oded Regev, On Lattices, Learning with Errors, Random Linear Codes, and Cryptography, full version dated May 2, 2009, https://cims.nyu.edu/~regev/papers/qcrypto.pdf. Finite-dimensional completion required by the original fixed-family Gaussian worst-case target (Appendix I.1); exact fixed-rank lattice algorithms and a uniform finite dispatcher. This is an explicit formalization obligation rather than a separately numbered Regev lemma.

import Definitions.Def_InfoLossLAR_RegevSketch_DGS

set_option autoImplicit false
set_option maxHeartbeats 200000
open QAlgorithms.Complexity
open scoped BigOperators Classical

namespace InfoLossLAR.WorstCase.RegevSketch

theorem finite_sivp_patch (A : MFamily) (hA : IsMQPT A) (cutoff : ℕ) (gamma : ℕ → ℝ)
    (hgamma : ∀ n,1 ≤ n → 1 ≤ gamma n) :
    ∃ patched : MFamily,IsMQPT patched ∧ ∀ n,1 ≤ n →
      (cutoff ≤ n → SolvesSIVP A (famN n) (gamma n)) →
        SolvesSIVP patched (famN n) (gamma n) := by sorry

end InfoLossLAR.WorstCase.RegevSketch
