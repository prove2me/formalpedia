-- Prove2me | Theorems.Thm_HananyPuder_exists_trace_youngAct_eq_aeval_and_linearIndependent_and_span_eq_top
-- name    : HananyPuder.exists_trace_youngAct_eq_aeval_and_linearIndependent_and_span_eq_top
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-11-06T08:32:17.113231+00:00
-- url     : https://prove2.me/theorems/209e10ad-579e-49c5-be64-e6fb60bd4b14
-- title:
--   Hanany–Puder, Proposition B.2 (full form) — the stable irreducible characters are polynomials in ξ₁, ξ₂, … and form a basis of ℚ[ξ₁, ξ₂, …]
-- statement:
--   There is a family of polynomials $q_\lambda \in \mathbb Q[\xi_1, \xi_2, \dots]$, one for each Young diagram $\lambda$ (as `MvPolynomial ℕ ℚ`, the variable $i$ standing for $\xi_{i+1}$), such that:
--
--   1. for every $\lambda$, every $N \ge |\lambda| + \lambda_1$ and every $\sigma \in \mathbf S_N$, the trace of $\sigma$ on the representation of $\mathbf S_N$ defined by $\lambda[N] = (N - |\lambda|, \lambda_1, \dots, \lambda_\ell)$ (`youngAct N (stableRows λ N)` on `youngSpace N (stableRows λ N)`) equals $q_\lambda$ evaluated in $\mathbb C$ at $\xi_j = \xi_j(\sigma)$, the number of fixed points of $\sigma^j$ (`StrongConv.xi j σ`); and
--   2. the $q_\lambda$ are linearly independent over $\mathbb Q$ and span $\mathbb Q[\xi_1, \xi_2, \dots]$, so they form a linear basis of it.
--
--   Here $|\lambda|$ is the number of cells of $\lambda$ and $\lambda_1$ its first row length. The empty diagram is included: $\lambda[N] = (N)$ is the trivial representation.
--
--   This is Proposition B.2 of Hanany–Puder in full. The published `HananyPuder.exists_linearEquiv_pi_youngSpace` is the form Chen–Garza-Vargas–Tropp–van Handel apply (every stable representation is a direct sum of such representations).
-- source:
--   Chen, C.-F., Garza-Vargas, J., Tropp, J. A. and van Handel, R., A new approach to strong convergence, Ann. of Math. (2) 203 (2026) 555–602, https://doi.org/10.4007/annals.2026.203.2.4 (arXiv:2405.16026v3, whose page numbers are used), p. 14, the proposition of Hanany–Puder cited in §3.4, in full, which cites Hanany, L. and Puder, D., Word measures on symmetric groups, Int. Math. Res. Not. IMRN 2023 (2023) 9221–9297, https://doi.org/10.1093/imrn/rnac084 (arXiv:2009.00897v4), Proposition B.2

import Mathlib
import Definitions.Def_StrongConv
import Definitions.Def_StrongConvG4

open StrongConv

namespace HananyPuder

theorem exists_trace_youngAct_eq_aeval_and_linearIndependent_and_span_eq_top :
    ∃ q : YoungDiagram → MvPolynomial ℕ ℚ,
      (∀ (μ : YoungDiagram) (N : ℕ), μ.cells.card + μ.rowLen 0 ≤ N →
        ∀ σ : Equiv.Perm (Fin N),
          LinearMap.trace ℂ (youngSpace N (stableRows μ N)) (youngAct N (stableRows μ N) σ) =
            MvPolynomial.aeval (fun i : ℕ => ((xi (i + 1) σ : ℕ) : ℂ)) (q μ)) ∧
      LinearIndependent ℚ q ∧ Submodule.span ℚ (Set.range q) = ⊤ := by
  sorry

end HananyPuder
