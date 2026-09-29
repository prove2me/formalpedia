-- Prove2me | Theorems.Thm_HeckeEis_exists_eq_smul_X_pow_of_binaryFormRepSL_T_zpow_eq_self
-- name    : HeckeEis.exists_eq_smul_X_pow_of_binaryFormRepSL_T_zpow_eq_self
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:55.342414+00:00
-- url     : https://prove2.me/theorems/37db5548-5371-5fa4-8056-cad4294d97e5
-- title:
--   Forms fixed by T^h are multiples of X₀ⁿ
-- statement:
--   Let $R$ be a commutative ring which is an integral domain, let $n$ be a natural number, and let $h$ be an integer whose image in $R$ is nonzero; assume further that for every natural number $j$ with $1 \le j \le n$ the image of $j$ in $R$ is nonzero. Let $P$ be an element of [`HeckeEis.BinaryForm R n`](def/HeckeEis_BinaryFormRep.html#L25), that is, of the submodule `MvPolynomial.homogeneousSubmodule (Fin 2) R n` of polynomials in $R[X_0,X_1]$ homogeneous of degree $n$ (the zero polynomial included). Suppose $P$ is fixed by the value at $\mathrm{T}^h$ of the representation [`HeckeEis.binaryFormRepSL R n`](def/HeckeEis_BinaryFormRep.html#L61) of $\mathrm{SL}_2(\mathbb{Z})$ on that submodule, where $\mathrm{T} = \begin{pmatrix}1&1\\0&1\end{pmatrix}$ is `ModularGroup.T` and a matrix $M$ acts by the $R$-algebra substitution $X_j \mapsto \sum_i \overline{M_{ij}}\,X_i$; for $M = \mathrm{T}^h$ this is the substitution $X_0 \mapsto X_0$, $X_1 \mapsto \overline{h}X_0 + X_1$, so the hypothesis reads $P(X_0, hX_0 + X_1) = P(X_0, X_1)$. The conclusion is that there is a scalar $c \in R$ with $P = c \cdot X_0^{\,n}$ as polynomials in $R[X_0,X_1]$.
--
--   This identifies the fixed subspace of the unipotent element $\mathrm{T}^h$ acting on binary forms of degree $n$ — the kernel half of the analysis of $\rho(\mathrm{T}^h) - 1$ on $\mathrm{Sym}^n$ — under the numerical hypotheses that $h$ and $1,\dots,n$ are invertible-enough (nonzero) in the domain $R$. It is used for the corresponding statement for the lower unipotent matrices, [`HeckeEis.exists_eq_smul_X_pow_of_binaryFormRepSL_lowerUnipotent_eq_self`](thm.html#HeckeEis.exists_eq_smul_X_pow_of_binaryFormRepSL_lowerUnipotent_eq_self), and in the vanishing result [`HeckeEis.coeffH1par_binaryFormRepSL_int_eq_zero_of_smul_eq_zero`](thm.html#HeckeEis.coeffH1par_binaryFormRepSL_int_eq_zero_of_smul_eq_zero) entering the study of parabolic cohomology with $\mathrm{Sym}^n$ coefficients.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_HeckeEis_exists_eq_smul_X_pow_of_binaryFormRepSL_T_zpow_eq_self.lean

import Mathlib
import Definitions.Def_HeckeEis_BinaryFormRep

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped MatrixGroups

theorem HeckeEis.exists_eq_smul_X_pow_of_binaryFormRepSL_T_zpow_eq_self {R : Type*} [CommRing R] [IsDomain R] (n : ℕ)
    {h : ℤ} (hh : (h : R) ≠ 0) (hn : ∀ j : ℕ, 1 ≤ j → j ≤ n → (j : R) ≠ 0) (P : ↥(HeckeEis.BinaryForm R n))
    (hP : HeckeEis.binaryFormRepSL R n (ModularGroup.T ^ h) P = P) :
    ∃ c : R, (P : MvPolynomial (Fin 2) R) = c • MvPolynomial.X 0 ^ n := by sorry
