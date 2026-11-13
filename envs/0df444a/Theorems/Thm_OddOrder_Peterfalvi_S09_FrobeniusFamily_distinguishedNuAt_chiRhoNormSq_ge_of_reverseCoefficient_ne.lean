-- Prove2me | Theorems.Thm_OddOrder_Peterfalvi_S09_FrobeniusFamily_distinguishedNuAt_chiRhoNormSq_ge_of_reverseCoefficient_ne
-- name    : OddOrder.Peterfalvi.S09.FrobeniusFamily.distinguishedNuAt_chiRhoNormSq_ge_of_reverseCoefficient_ne
-- status  : Proved
-- author  : @burkh4rt
-- created : 2026-11-12T08:26:15.080354+00:00
-- url     : https://prove2.me/theorems/dc2c4c5a-9078-4f94-acc0-3ecf6fc421d1
-- title:
--   Peterfalvi (7.8.c): rho-norm lower bound when a reverse coefficient is nonzero
-- statement:
--   Let $G$ be a finite group of odd order, and let $F$ be a Frobenius family in $G$ (`FrobeniusFamily G k`): subgroups $L_j,H_j\le G$ ($j<k$, $k\ge 2$) with $H_j\le L_j$, each $L_j$ a Frobenius group with kernel $H_j$, $L_j=N_G(H_j)$, $H_j^\#$ a TI-subset with normalizer $L_j$, and the orders $|H_j|$ pairwise coprime. For every $j<k$ assume the kernel $H_j$ is nilpotent and that $C_j\le L_j$ is a Frobenius complement (`IsFrobeniusGroup L_j H_j (C j)`); the canonical (7.8) data of each member are then defined.
--
--   Let $i\ne j$ be family indices such that $\langle\beta_j,N_i\rangle\ne0$, where $\beta_j=$ `betaAt j` and $N_i=$ `distinguishedNuAt i`. Then
--   $$\frac{h_j-1}{e_j\,h_j}\ \le\ \texttt{chiRhoNormSq}(N_i)\ j ,$$
--   where $h_j=|H_j|$, $e_j=|L_j:H_j|$, and `chiRhoNormSq` (of `F.familyHypothesis71`) is the $\rho_j$-norm squared of a class function.
--
--   This is the concrete good-index bound of Peterfalvi (7.8.c) used in the (7.10) estimate.
--
--   **Formalization Note.** The ambient `Fintype`/`Invertible (Nat.card · : ℂ)` instances for $G$, $L_i$ and the kernel, and the normality instance for the kernel in $L_i$, are explicit hypotheses; they are automatic mathematically. Oddness of $|G|$ is the hypothesis `hodd : Odd (Nat.card G)`.
-- source:
--   Yawara Ishida, Lean 4 formalization of the Feit–Thompson (odd order) theorem, github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0), https://github.com/yawara/odd-order/blob/20a6fccbb63c0b138acda9f7fafd798c42f9441b/OddOrder/Peterfalvi/S09_FrobeniusGoodIndexEstimate.lean#L59-L193

import Definitions.Def_OddOrder_Peterfalvi_S09_FrobeniusGammaNormEstimate
import Definitions.Def_OddOrder_Peterfalvi_S09_NonexistenceCertain_FrobeniusFamily

namespace OddOrder.Peterfalvi.S09

open OddOrder.RepresentationTheory

namespace FrobeniusFamily

variable {G : Type*} [Group G] {k : ℕ}

section GoodIndex

variable [Fintype G] [Invertible (Nat.card G : ℂ)]

variable (F : FrobeniusFamily G k) (hodd : Odd (Nat.card G))

variable (hnilp : ∀ j : Fin k,
  Group.IsNilpotent ↥((F.H j).subgroupOf (F.L j)))

variable (C : ∀ j : Fin k, Subgroup ↥(F.L j))

variable (hFrob : ∀ j : Fin k, OddOrder.Isaacs.Ch06.IsFrobeniusGroup
  ↥(F.L j) ((F.H j).subgroupOf (F.L j)) (C j))

theorem distinguishedNuAt_chiRhoNormSq_ge_of_reverseCoefficient_ne
    (i j : Fin k) (hij : i ≠ j)
    (hcoeff : ClassFunction.inner
      (F.betaAt hodd hnilp C hFrob j)
      (F.distinguishedNuAt hodd hnilp C hFrob i) ≠ 0) :
    ((F.h j : ℝ) - 1) / ((F.e j : ℝ) * (F.h j : ℝ)) ≤
      (F.familyHypothesis71).chiRhoNormSq
        (F.distinguishedNuAt hodd hnilp C hFrob i) j := by sorry

end GoodIndex

end FrobeniusFamily

end OddOrder.Peterfalvi.S09
