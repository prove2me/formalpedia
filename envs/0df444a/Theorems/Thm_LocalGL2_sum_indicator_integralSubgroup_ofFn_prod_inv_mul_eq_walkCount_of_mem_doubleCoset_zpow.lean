-- Prove2me | Theorems.Thm_LocalGL2_sum_indicator_integralSubgroup_ofFn_prod_inv_mul_eq_walkCount_of_mem_doubleCoset_zpow
-- name    : LocalGL2.sum_indicator_integralSubgroup_ofFn_prod_inv_mul_eq_walkCount_of_mem_doubleCoset_zpow
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:11.015121+00:00
-- url     : https://prove2.me/theorems/67a7ecdd-bd92-560d-a87c-ad8fd75be3e8
-- title:
--   Counting Hecke words of length k by tree walk numbers
-- statement:
--   Let $R$ be a discrete valuation domain with fraction field $K$, and let $\varpi\in R$ be irreducible with nonzero image in $K$ and with finite residue ring $R/(\varpi)$; write $q=\#(R/(\varpi))$ and $U=\mathrm{GL}_2(R)$ for the image of $\mathrm{GL}_2(R)$ in $\mathrm{GL}_2(K)$ under the structure map (`integralSubgroup`). Put $P=\mathrm{diag}(\varpi,1)$ (`diagPi`) and $Q=w\,P\,w$ (`localRepInf`), where $w$ is the image in $\mathrm{GL}_2(K)$ of the matrix `weylR` over $R$. Let $\iota$ be a finite type and $r\colon\iota\to\mathrm{GL}_2(K)$ a Hecke coset system for $U$ and $P$: each $r_i$ lies in $U\{P\}U$, every element of $U\{P\}U$ lies in some coset $r_iU$, and $i\mapsto r_iU$ is injective. Let $W\colon\mathbb N\times\mathbb N\to\mathbb N$ satisfy $W(0,0)=1$, $W(0,d+1)=0$, $W(k+1,0)=(q+1)W(k,1)$ and $W(k+1,d+1)=W(k,d)+q\,W(k,d+2)$. Then for all $k\in\mathbb N$, $a,b\in\mathbb Z$ and $y\in U\{P^aQ^b\}U$, the sum over all words $w\colon\{0,\dots,k-1\}\to\iota$ of the indicator of $U$ (with value $1$) at $(r_{w(0)}\cdots r_{w(k-1)})^{-1}y$ equals $W(k,|a-b|)$ if $a+b=k$, and $0$ otherwise.
--
--   This is the dictionary between words in the $U$-cosets of the double coset $UPU$ and walks of length $k$ in the $(q+1)$-regular Bruhat–Tits tree of $\mathrm{PGL}_2(K)$: a word contributes exactly when the Cartan invariants $(a,b)$ of $y$ have $a+b=k$, and the count then depends only on the distance $|a-b|$. It is used in the computation of Satake combinations and of weighted orbital integrals of Hecke words in the automorphic part of the argument.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LocalGL2_sum_indicator_integralSubgroup_ofFn_prod_inv_mul_eq_walkCount_of_mem_doubleCoset_zpow.lean

import Definitions.Def_LocalLanglands_HeckeCosetLocal
import Definitions.Def_LocalLanglands_HeckePair
import Definitions.Def_LocalLanglands_HeckeCosetSystem

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem LocalGL2.sum_indicator_integralSubgroup_ofFn_prod_inv_mul_eq_walkCount_of_mem_doubleCoset_zpow
    {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]
    (ϖ : R) (hϖ0 : algebraMap R K ϖ ≠ 0) (hϖ : Irreducible ϖ) [Finite (R ⧸ Ideal.span {ϖ})]
    {ι : Type*} [Fintype ι] (r : ι → GL (Fin 2) K)
    (hr : HeckeIntegralSeam.IsHeckeCosetSystem (LocalGL2.integralSubgroup R K) (LocalGL2.diagPi ϖ hϖ0) r)
    (W : ℕ → ℕ → ℕ) (h00 : W 0 0 = 1) (h0s : ∀ d : ℕ, W 0 (d + 1) = 0)
    (hroot : ∀ k : ℕ, W (k + 1) 0 = (Nat.card (R ⧸ Ideal.span {ϖ}) + 1) * W k 1)
    (hstep : ∀ k d : ℕ, W (k + 1) (d + 1) = W k d + Nat.card (R ⧸ Ideal.span {ϖ}) * W k (d + 2))
    (k : ℕ) (a b : ℤ) (y : GL (Fin 2) K)
    (hy : y ∈ HeckePair.doubleCoset (LocalGL2.integralSubgroup R K)
      (LocalGL2.diagPi ϖ hϖ0 ^ a * LocalGL2.localRepInf ϖ hϖ0 ^ b)) :
    ∑ w : Fin k → ι, (LocalGL2.integralSubgroup R K : Set (GL (Fin 2) K)).indicator (fun _ => (1 : ℕ))
        (((List.ofFn fun j => r (w j)).prod)⁻¹ * y) =
      if a + b = k then W k (a - b).natAbs else 0 := by sorry
