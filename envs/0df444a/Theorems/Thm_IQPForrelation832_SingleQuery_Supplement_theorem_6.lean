-- Prove2me | Theorems.Thm_IQPForrelation832_SingleQuery_Supplement_theorem_6
-- name    : IQPForrelation832.SingleQuery.Supplement.theorem_6
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T20:58:24.876727+00:00
-- url     : https://prove2.me/theorems/cebaafc0-ce0f-40ba-9893-9a8e11998734
-- title:
--   Theorem 6 — exact asymmetric binomial Fourier-level bound
-- statement:
--   Let $p$ be the actual acceptance probability of any $d$-query IQP circuit using a single $n$-wire phase oracle and any accepting subset of the computational basis. Set $N=2^n$, the original oracle-table length. For every restriction $\rho$, the function $p|\rho$ is multilinear of degree at most $2d$. For each natural level $\ell\le2d$,
--   $$
--   L_{1,\ell}(p|\rho)\le
--   \sum_{\substack{0\le a,b\le d\\a+b=\ell}}
--   \sqrt{\min\left\{\binom da\binom Nb,\binom db\binom Na\right\}},
--   $$
--   and $L_{1,\ell}(p|\rho)=0$ for $\ell>2d$. The minimum stays inside each square root; no geometric-mean or asymptotic relaxation is made. $N$ remains the original table length after every restriction. There is no assumption that $d\le N$, or that $n,m,d$ are positive. Arbitrary diagonal-unitary middle gates, ancillas, overlapping queries, repeated addresses and all accepting subsets are included. This companion theorem gives the exact level-wise query bound, using the restricted decomposition of Lemma 5.
--
--   Differences from the source:
--   - generalization: polynomial-size IQP middle blocks → arbitrary finite diagonal-unitary middle gate lists; reason: the Section 5 arguments do not use the number of non-oracle gates; every source circuit is included
--   - encoding: sign assignments on the free set Gamma and its subsets → Boolean signs on the exact free-coordinate subtype; reason: true represents +1 and false represents -1; all assignments and restrictions correspond bijectively, including the empty free set
-- source:
--   Quentin Buzet, André Chailloux, IQP circuits for 2-Forrelation, STOC 2027 submission #832 (October 2026), p. 27, Theorem 6; proof pp. 27-30. https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/832.pdf

import Definitions.Def_IQPForrelation832_SingleQuery_Supplement_OracleFourier

set_option autoImplicit false

namespace IQPForrelation832.SingleQuery.Supplement

open QAlgorithms QAlgorithms.Complexity

theorem theorem_6 {n m d : ℕ} (c : PhaseMiddle n m)
    (hc : PhaseIQP c) (hd : OracleCircuit.queryCount c 0 = d)
    (F : Finset (Qubits m)) (ρ : Restriction n) :
    MultilinearDegreeLE (phaseBorn c F) ρ (2*d) ∧
    (∀ ell : ℕ, ell ≤ 2*d → levelMass (phaseBorn c F) ρ ell ≤ binomialBound d (2^n) ell) ∧
    (∀ ell : ℕ, 2*d < ell → levelMass (phaseBorn c F) ρ ell = 0) := by sorry

end IQPForrelation832.SingleQuery.Supplement
