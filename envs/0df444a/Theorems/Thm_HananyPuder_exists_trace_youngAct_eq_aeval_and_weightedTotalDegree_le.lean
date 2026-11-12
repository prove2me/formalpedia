-- Prove2me | Theorems.Thm_HananyPuder_exists_trace_youngAct_eq_aeval_and_weightedTotalDegree_le
-- name    : HananyPuder.exists_trace_youngAct_eq_aeval_and_weightedTotalDegree_le
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-11T19:39:03.238194+00:00
-- url     : https://prove2.me/theorems/75f41e58-c635-4a9e-8da0-51e1d46d1d74
-- title:
--   Hanany–Puder, proof of Proposition B.2 — the stable irreducible characters are polynomials in ξ₁, ξ₂, … of weighted degree at most |λ|
-- statement:
--   There is a family of polynomials $q_\lambda \in \mathbb Q[\xi_1, \xi_2, \dots]$, one for each Young diagram $\lambda$ (as `MvPolynomial ℕ ℚ`, the variable $i$ standing for $\xi_{i+1}$), such that:
--
--   1. for every $\lambda$, every $N \ge |\lambda| + \lambda_1$ and every $\sigma \in \mathbf S_N$, the trace of $\sigma$ on the representation of $\mathbf S_N$ defined by $\lambda[N] = (N - |\lambda|, \lambda_1, \dots, \lambda_\ell)$ (`youngAct N (stableRows λ N)` on `youngSpace N (stableRows λ N)`) equals $q_\lambda$ evaluated in $\mathbb C$ at $\xi_j = \xi_j(\sigma)$, the number of fixed points of $\sigma^j$ (`StrongConv.xi j σ`); and
--   2. $q_\lambda$ has weighted degree at most $|\lambda|$ when $\xi_j$ is given weight $j$ (`MvPolynomial.weightedTotalDegree` with weight $i + 1$ on the variable $i$).
--
--   Here $|\lambda|$ is the number of cells of $\lambda$ and $\lambda_1$ its first row length. The empty diagram is included.
--
--   This is what the proof of Hanany–Puder's Proposition B.2 (pp. 46–47) takes from formula (B.1), which it cites from Macdonald (*Symmetric Functions and Hall Polynomials*, I.7 Ex. 14). (B.1) writes $\chi_N$ as a combination of the $\binom{a}{\rho}$ with $|\rho| \le |\lambda|$, where $a_t$ counts the $t$-cycles. HP: "the formula (B.1) shows that as elements in $\mathcal A$, they are spanned by the monomials $a_1^{m_1} a_2^{m_2} \cdots a_k^{m_k}$ with $m_1 + 2m_2 + \dots + km_k \le k$". Since $\xi_j = \sum_{t \mid j} t\, a_t$ (p. 46), weighted degree in the $a_t$ (weight $t$) and in the $\xi_j$ (weight $j$) agree. The rest of HP's proof, a dimension count, turns this into Proposition B.2 in full (`HananyPuder.exists_trace_youngAct_eq_aeval_and_linearIndependent_and_span_eq_top`).
-- source:
--   Hanany, L. and Puder, D., Word measures on symmetric groups, Int. Math. Res. Not. IMRN 2023 (2023) 9221–9297, https://doi.org/10.1093/imrn/rnac084 (arXiv:2009.00897v4), pp. 46–47, Proposition B.2, the consequence of formula (B.1) used in its proof

import Mathlib
import Definitions.Def_StrongConv
import Definitions.Def_StrongConvG4

open StrongConv

namespace HananyPuder

theorem exists_trace_youngAct_eq_aeval_and_weightedTotalDegree_le :
    ∃ q : YoungDiagram → MvPolynomial ℕ ℚ,
      (∀ (μ : YoungDiagram) (N : ℕ), μ.cells.card + μ.rowLen 0 ≤ N →
        ∀ σ : Equiv.Perm (Fin N),
          LinearMap.trace ℂ (youngSpace N (stableRows μ N)) (youngAct N (stableRows μ N) σ) =
            MvPolynomial.aeval (fun i : ℕ => ((xi (i + 1) σ : ℕ) : ℂ)) (q μ)) ∧
      ∀ μ : YoungDiagram, MvPolynomial.weightedTotalDegree (fun i : ℕ => i + 1) (q μ) ≤ μ.cells.card := by
  sorry

end HananyPuder
