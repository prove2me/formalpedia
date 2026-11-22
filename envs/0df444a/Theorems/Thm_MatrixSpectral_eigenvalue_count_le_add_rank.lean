-- Prove2me | Theorems.Thm_MatrixSpectral_eigenvalue_count_le_add_rank
-- name    : MatrixSpectral.eigenvalue_count_le_add_rank
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-11-22T21:24:31.146691+00:00
-- url     : https://prove2.me/theorems/0bf48312-382b-4f68-83dc-6675984a066b
-- title:
--   Rank inequality for eigenvalue counting functions
-- statement:
--   Let $U$ and $V$ be Hermitian $d\times d$ complex matrices, with eigenvalues (listed with multiplicity) $\lambda_1(U),\dots,\lambda_d(U)$ and $\lambda_1(V),\dots,\lambda_d(V)$. For $t\in\mathbb R$ write
--   $$N_U(t)=\#\{i:\lambda_i(U)\le t\},\qquad N^U(t)=\#\{i:\lambda_i(U)\ge t\}$$
--   for the number of eigenvalues of $U$ that are at most $t$ and at least $t$, and similarly for $V$. Then for every $t$,
--   $$N_U(t)\le N_V(t)+\operatorname{rank}(U-V),\qquad N^U(t)\le N^V(t)+\operatorname{rank}(U-V).$$
--
--   Exchanging $U$ and $V$ gives $|N_U(t)-N_V(t)|\le\operatorname{rank}(U-V)$, the rank inequality for empirical spectral distribution functions. This is the spectral counting bound used for low-rank perturbations of trace functionals.
--
--   **Formalization Note** Eigenvalues are Mathlib's `Matrix.IsHermitian.eigenvalues`, indexed by `Fin d`. The counts are cardinalities of filtered index sets, so they do not depend on how the eigenvalues are ordered. The second inequality is the same statement for closed upper half-lines; it is equivalent to the first one applied to $-U$ and $-V$.
-- source:
--   Z. Bai and J. W. Silverstein, Spectral Analysis of Large Dimensional Random Matrices, 2nd ed., Springer 2010, Appendix A, Theorem A.43 (rank inequality); cited as [BS10, Theorem A.43] in Chen–Gao–Wang, Optimal Trace Distance Estimation, STOC 2027 submission #875, p.25 (proof of Lemma 2.4), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/875.pdf

import Mathlib

open scoped Matrix

namespace MatrixSpectral

theorem eigenvalue_count_le_add_rank {d : ℕ} (U V : Matrix (Fin d) (Fin d) ℂ)
    (hU : U.IsHermitian) (hV : V.IsHermitian) (t : ℝ) :
    (Finset.univ.filter (fun i => hU.eigenvalues i ≤ t)).card ≤
        (Finset.univ.filter (fun i => hV.eigenvalues i ≤ t)).card + (U - V).rank ∧
    (Finset.univ.filter (fun i => t ≤ hU.eigenvalues i)).card ≤
        (Finset.univ.filter (fun i => t ≤ hV.eigenvalues i)).card + (U - V).rank := by sorry

end MatrixSpectral
