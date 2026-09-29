-- Prove2me | Theorems.Thm_HeckeEis_exists_eq_smul_X_pow_of_binaryFormRepSL_lowerUnipotent_eq_self
-- name    : HeckeEis.exists_eq_smul_X_pow_of_binaryFormRepSL_lowerUnipotent_eq_self
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:55.342414+00:00
-- url     : https://prove2.me/theorems/f0572a19-e7e9-5a76-9764-969b69c4c9d7
-- title:
--   Fixed forms of a lower unipotent are multiples of X₁ⁿ
-- statement:
--   Let $R$ be a commutative ring which is an integral domain, let $n$ be a natural number, and let $h$ be an integer whose image in $R$ is nonzero; assume moreover that the image in $R$ of every integer $j$ with $1 \le j \le n$ is nonzero. Let $g$ be an element of $\mathrm{SL}_2(\mathbb{Z})$ whose underlying $2\times 2$ integer matrix is $!![1,0;h,1]$, and let $P$ belong to [`HeckeEis.BinaryForm R n`](def/HeckeEis_BinaryFormRep.html#L25), i.e. the submodule of $R$-homogeneous polynomials of degree $n$ in $R[X_0,X_1] =$ `MvPolynomial (Fin 2) R`. The action used is [`HeckeEis.binaryFormRepSL R n`](def/HeckeEis_BinaryFormRep.html#L61), the representation of $\mathrm{SL}_2(\mathbb{Z})$ on this submodule induced by the substitution algebra endomorphism [`HeckeEis.binarySubst`](def/HeckeEis_BinaryFormRep.html#L28), which sends $X_j$ to $\sum_{i} M_{ij} X_i$ for the matrix $M$ of the group element; for $M = !![1,0;h,1]$ this is $X_0 \mapsto X_0 + hX_1$, $X_1 \mapsto X_1$. Assume that $P$ is fixed by $g$ under this action, that is $P(X_0 + hX_1, X_1) = P(X_0,X_1)$. The conclusion is that there exists $c \in R$ with $P = c \cdot X_1^{\,n}$ as elements of $R[X_0,X_1]$.
--
--   This is the determination of the fixed subspace of a lower triangular unipotent matrix acting on binary forms of degree $n$ (the symmetric power $\mathrm{Sym}^n$ of the standard representation), in the case where $h$ and the integers $1,\dots,n$ are invertible enough to be nonzero in $R$: the fixed vectors form the line spanned by $X_1^n$. It is applied to $\begin{pmatrix}1&0\\N&1\end{pmatrix} \in \Gamma_0(N)$ in the proof that certain parabolic cohomology classes vanish, namely in [`HeckeEis.coeffH1par_binaryFormRepSL_int_eq_zero_of_smul_eq_zero`](thm.html#HeckeEis.coeffH1par_binaryFormRepSL_int_eq_zero_of_smul_eq_zero). The group element is specified by its matrix rather than by a fixed presentation, so any element with that matrix may be used.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_HeckeEis_exists_eq_smul_X_pow_of_binaryFormRepSL_lowerUnipotent_eq_self.lean

import Mathlib
import Definitions.Def_HeckeEis_BinaryFormRep

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped MatrixGroups

theorem HeckeEis.exists_eq_smul_X_pow_of_binaryFormRepSL_lowerUnipotent_eq_self {R : Type*} [CommRing R] [IsDomain R] (n : ℕ)
    {h : ℤ} (hh : (h : R) ≠ 0) (hn : ∀ j : ℕ, 1 ≤ j → j ≤ n → (j : R) ≠ 0)
    (g : SL(2, ℤ)) (hg : (g : Matrix (Fin 2) (Fin 2) ℤ) = !![1, 0; h, 1])
    (P : ↥(HeckeEis.BinaryForm R n)) (hP : HeckeEis.binaryFormRepSL R n g P = P) :
    ∃ c : R, (P : MvPolynomial (Fin 2) R) = c • MvPolynomial.X 1 ^ n := by sorry
