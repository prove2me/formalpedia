-- Prove2me | Theorems.Thm_InfoLossLAR_WorstCase_RegevSketch_finite_gap_patch
-- name    : InfoLossLAR.WorstCase.RegevSketch.finite_gap_patch
-- status  : Open
-- author  : @BoomShaKaLaaaKa
-- created : 2026-11-15T01:15:18.0822+00:00
-- url     : https://prove2.me/theorems/d1bfdc46-e1c2-4fe2-8bb4-b595a89e5e70
-- title:
--   Uniform finite-dimensional patch for GapSVP solvers
-- statement:
--   Let $A$ be a uniform quantum polynomial-time decision algorithm, let $n_0$ be a fixed natural-number cutoff, and let $\gamma:\mathbb N\to\mathbb R$ satisfy $\gamma(n)\ge1$ at positive dimensions. There is a uniform quantum polynomial-time algorithm $\widetilde A$ such that, for every positive $n$,
--
--   $$
--   \bigl(n\ge n_0\ \Longrightarrow\ A\text{ solves }\mathrm{GapSVP}_{\gamma(n)}\bigr)
--   \ \Longrightarrow\
--   \widetilde A\text{ solves }\mathrm{GapSVP}_{\gamma(n)}.
--   $$
--
--   Every solver guarantee quantifies over all nonsingular integer bases and positive rational promise thresholds. Thus the finitely many dimensions below $n_0$ still contain infinitely many binary-coded inputs.
--
--   This formalization obligation combines exact fixed-rank lattice algorithms with a uniform family that inherits the given solver’s guarantee above the cutoff. It extends an eventual guarantee to all positive dimensions and makes no computability assumption on $\gamma$. It is not a finite lookup table of lattice instances.
-- source:
--   Oded Regev, On Lattices, Learning with Errors, Random Linear Codes, and Cryptography, full version dated May 2, 2009, https://cims.nyu.edu/~regev/papers/qcrypto.pdf. Finite-dimensional completion required by the original fixed-family Gaussian worst-case target (Appendix I.1); uses exact fixed-rank lattice algorithms and a uniform finite dispatcher. This patch is an explicit formalization obligation, not a separately numbered lemma in Regev.

import Definitions.Def_InfoLossLAR_RegevSketch_DGS

set_option autoImplicit false
set_option maxHeartbeats 200000
open QAlgorithms.Complexity
open scoped BigOperators Classical

namespace InfoLossLAR.WorstCase.RegevSketch

theorem finite_gap_patch (A : Family) (hA : IsQPT A) (cutoff : ℕ) (gamma : ℕ → ℝ)
    (hgamma : ∀ n,1 ≤ n → 1 ≤ gamma n) :
    ∃ patched : Family,IsQPT patched ∧ ∀ n,1 ≤ n →
      (cutoff ≤ n → SolvesGapSVP A (famN n) (gamma n)) →
        SolvesGapSVP patched (famN n) (gamma n) := by sorry

end InfoLossLAR.WorstCase.RegevSketch
