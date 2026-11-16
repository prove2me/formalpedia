-- Prove2me | Theorems.Thm_IQPForrelation832_SingleQuery_Supplement_theorem_5
-- name    : IQPForrelation832.SingleQuery.Supplement.theorem_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T20:57:58.627442+00:00
-- url     : https://prove2.me/theorems/4411da52-47da-4b9f-932d-eb38a33d0cef
-- title:
--   Theorem 5 — total and level Fourier mass from the accepting-set size
-- statement:
--   Let $p$ be the actual acceptance probability of any $d$-query IQP circuit with any accepting subset $F$ of the $m$-bit computational basis. For every restriction $\rho$, the restricted function has its multilinear Fourier expansion of degree at most $2d$, and
--   $$
--   \sum_{S\subseteq\Gamma}|\widehat{p|\rho}(S)|\le\sqrt{|F|}.
--   $$
--   In particular, for every natural level $\ell$,
--   $$
--   L_{1,\ell}(p|\rho)\le\sqrt{|F|}\quad(\ell\le2d),\qquad
--   L_{1,\ell}(p|\rho)=0\quad(\ell>2d).
--   $$
--   The sum includes the constant coefficient. The constant is exactly one, the acceptance event is the unconditioned Born event, and $F$ can be empty. Every restriction, query overlap, repeated address, ancilla width and zero-query case is retained. This companion theorem bounds total Fourier mass by the actual accepting-set size, independently of the query-dependent bound of Theorem 6.
--
--   Differences from the source:
--   - generalization: polynomial-size IQP middle blocks → arbitrary finite diagonal-unitary middle gate lists; reason: the Section 5 arguments do not use the number of non-oracle gates; every source circuit is included
--   - encoding: sign assignments on the free set Gamma and its subsets → Boolean signs on the exact free-coordinate subtype; reason: true represents +1 and false represents -1; all assignments and restrictions correspond bijectively, including the empty free set
-- source:
--   Quentin Buzet, André Chailloux, IQP circuits for 2-Forrelation, STOC 2027 submission #832 (October 2026), p. 26, Theorem 5; proof pp. 26-27. https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/832.pdf

import Definitions.Def_IQPForrelation832_SingleQuery_Supplement_OracleFourier

set_option autoImplicit false

namespace IQPForrelation832.SingleQuery.Supplement

open QAlgorithms QAlgorithms.Complexity

theorem theorem_5 {n m d : ℕ} (c : PhaseMiddle n m)
    (hc : PhaseIQP c) (hd : OracleCircuit.queryCount c 0 = d)
    (F : Finset (Qubits m)) (ρ : Restriction n) :
    MultilinearDegreeLE (phaseBorn c F) ρ (2*d) ∧
    totalMass (phaseBorn c F) ρ ≤ Real.sqrt (F.card : ℝ) ∧
    (∀ ell : ℕ, ell ≤ 2*d → levelMass (phaseBorn c F) ρ ell ≤ Real.sqrt (F.card : ℝ)) ∧
    (∀ ell : ℕ, 2*d < ell → levelMass (phaseBorn c F) ρ ell = 0) := by sorry

end IQPForrelation832.SingleQuery.Supplement
