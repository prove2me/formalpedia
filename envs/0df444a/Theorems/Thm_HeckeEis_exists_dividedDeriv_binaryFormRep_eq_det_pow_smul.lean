-- Prove2me | Theorems.Thm_HeckeEis_exists_dividedDeriv_binaryFormRep_eq_det_pow_smul
-- name    : HeckeEis.exists_dividedDeriv_binaryFormRep_eq_det_pow_smul
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:55.342414+00:00
-- url     : https://prove2.me/theorems/a1e9c713-2a02-53c1-9712-f2038ed5b57b
-- title:
--   Divided a-th derivative partial₀ᵃ/X₁ᵃ with detᵃ-equivariance
-- statement:
--   Let $p$ be a prime, let $K$ be a field of characteristic $p$, and let $a$ be a natural number. Write $\mathrm{BinaryForm}\,K\,n$ for the $K$-submodule of homogeneous polynomials of degree $n$ in $K[X_0,X_1]$, and let $\mathrm{binaryFormRep}\,K\,n$ be the monoid homomorphism sending an integral $2\times 2$ matrix $M$ to the endomorphism of $\mathrm{BinaryForm}\,K\,n$ induced by the $K$-algebra substitution $X_j\mapsto\sum_{i}(M_{ij}\bmod p)X_i$. The assertion is that there exists a $K$-linear map $D:\mathrm{BinaryForm}\,K\,(a+(p-1))\to\mathrm{BinaryForm}\,K\,(p-1-a)$ (truncated subtraction of naturals throughout) with three properties. First, for every $F$ in the source the underlying polynomial of $DF$ is $\sum_{a\le k<p}\bigl(c_k\cdot k(k-1)\cdots(k-a+1)\bigr)X_0^{k-a}X_1^{p-1-k}$, where $c_k$ denotes the coefficient of $X_0^{k}X_1^{a+p-1-k}$ in $F$ and the falling factorial is $k$'s descending factorial of length $a$, taken in $K$. Secondly, $X_1^{a}\cdot DF$ equals the $a$-fold iterate of the partial derivative $\partial/\partial X_0$ applied to $F$. Thirdly, for every integral $2\times 2$ matrix $M$, with no invertibility hypothesis, $D\bigl(\mathrm{binaryFormRep}\,K\,(a+(p-1))\,M\,F\bigr)=(\det M)^{a}\cdot\mathrm{binaryFormRep}\,K\,(p-1-a)\,M\,(DF)$, the determinant being taken in $\mathbb{Z}$ and mapped into $K$.
--
--   This is the divided $a$-th derivative $\partial_0^{a}/X_1^{a}$ relating the symmetric powers $\mathrm{Sym}^{a+p-1}$ and $\mathrm{Sym}^{p-1-a}$ of the standard two-dimensional representation in characteristic $p$, together with its $\det^{a}$-twisted equivariance for the substitution action of integral matrices. It supplies the connecting maps used in the analysis of the filtration of binary forms of degree $a+p-1$ by subquotients of degree at most $p-1$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_HeckeEis_exists_dividedDeriv_binaryFormRep_eq_det_pow_smul.lean

import Mathlib
import Definitions.Def_HeckeEis_BinaryFormRep
import Definitions.Def_Gamma0CoeffCohomology
import Definitions.Def_Gamma0CoeffCohomologyEigen

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MvPolynomial in

theorem HeckeEis.exists_dividedDeriv_binaryFormRep_eq_det_pow_smul (p : ℕ) [Fact p.Prime]
    (K : Type*) [Field K] [CharP K p] (a : ℕ) :
    ∃ D : ↥(HeckeEis.BinaryForm K (a + (p - 1))) →ₗ[K] ↥(HeckeEis.BinaryForm K (p - 1 - a)),
      (∀ F : ↥(HeckeEis.BinaryForm K (a + (p - 1))),
        ((D F : ↥(HeckeEis.BinaryForm K (p - 1 - a))) : MvPolynomial (Fin 2) K)
          = ∑ k ∈ Finset.Ico a p,
              monomial (Finsupp.single 0 (k - a) + Finsupp.single 1 (p - 1 - k))
                (coeff (Finsupp.single 0 k + Finsupp.single 1 (a + (p - 1) - k))
                  (F : MvPolynomial (Fin 2) K) * (k.descFactorial a : K))) ∧
      (∀ F : ↥(HeckeEis.BinaryForm K (a + (p - 1))),
        (X 1 : MvPolynomial (Fin 2) K) ^ a
            * ((D F : ↥(HeckeEis.BinaryForm K (p - 1 - a))) : MvPolynomial (Fin 2) K)
          = (fun G : MvPolynomial (Fin 2) K => pderiv 0 G)^[a] (F : MvPolynomial (Fin 2) K)) ∧
      (∀ (M : Matrix (Fin 2) (Fin 2) ℤ) (F : ↥(HeckeEis.BinaryForm K (a + (p - 1)))),
        D (HeckeEis.binaryFormRep K (a + (p - 1)) M F)
          = (((M.det : ℤ) : K) ^ a) • HeckeEis.binaryFormRep K (p - 1 - a) M (D F)) := by sorry
