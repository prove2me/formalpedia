-- Prove2me | Theorems.Thm_OddOrder_Peterfalvi_S09_FrobeniusFamily_hypothesis78_weightedNuSum_inner_self_eq
-- name    : OddOrder.Peterfalvi.S09.FrobeniusFamily.hypothesis78_weightedNuSum_inner_self_eq
-- status  : Proved
-- author  : @burkh4rt
-- created : 2026-11-12T08:22:44.906118+00:00
-- url     : https://prove2.me/theorems/98b6394e-1cd4-43f1-af20-be8762f2c357
-- title:
--   Peterfalvi (7.10): norm of the weighted coherent sum is $(h_i-1)/e_i$
-- statement:
--   Let $G$ be a finite group of odd order, and let $F$ be a Frobenius family in $G$ (`FrobeniusFamily G k`): subgroups $L_j,H_j\le G$ ($j<k$, $k\ge 2$) with $H_j\le L_j$, each $L_j$ a Frobenius group with kernel $H_j$, $L_j=N_G(H_j)$, $H_j^\#$ a TI-subset with normalizer $L_j$, and the orders $|H_j|$ pairwise coprime. Fix a member $i<k$, assume the kernel $H_i$ (as a subgroup of $L_i$) is nilpotent, and let $C\le L_i$ be a subgroup with `IsFrobeniusGroup L_i H_i C` (a Frobenius complement). These data determine the canonical Peterfalvi (7.8) coherence datum $\mathcal H=$ `F.hypothesis78 i hodd hnilp C hFrob`, with fields such as `hyp76.zeta`, `ind1H`, `zetaDistinct`, `nu`, `beta`, `delta`.
--
--   Let $h_i=|H_i|$ and $e_i=|L_i|/|H_i|$ (`F.h i`, `F.e i`) and let $W=$ `weightedNuSum` be the weighted sum of the coherent images $\nu(\zeta_r)$ over the non-principal members. Then
--   $$\langle W,W\rangle=\frac{h_i-1}{e_i}.$$
--
--   This is the local norm computation feeding the weighted Gamma decomposition in Peterfalvi (7.10).
--
--   **Formalization Note.** The ambient `Fintype`/`Invertible (Nat.card · : ℂ)` instances for $G$, $L_i$ and the kernel, and the normality instance for the kernel in $L_i$, are explicit hypotheses; they are automatic mathematically. Oddness of $|G|$ is the hypothesis `hodd : Odd (Nat.card G)`.
-- source:
--   Yawara Ishida, Lean 4 formalization of the Feit–Thompson (odd order) theorem, github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0), https://github.com/yawara/odd-order/blob/20a6fccbb63c0b138acda9f7fafd798c42f9441b/OddOrder/Peterfalvi/S09_FrobeniusFamilyOrthogonality.lean#L444-L555

import Definitions.Def_OddOrder_Peterfalvi_S09_FrobeniusConjIndex

namespace OddOrder.Peterfalvi.S09

open OddOrder.RepresentationTheory

namespace FrobeniusFamily

variable {G : Type*} [Group G] {k : ℕ}

section WeightedNorm

variable [Fintype G] [Invertible (Nat.card G : ℂ)]

variable (F : FrobeniusFamily G k) (i : Fin k) (hodd : Odd (Nat.card G))

variable [Fintype ↥(F.L i)] [Invertible (Nat.card ↥(F.L i) : ℂ)]

variable [Invertible (Nat.card ↥((F.H i).subgroupOf (F.L i)) : ℂ)]

variable [((F.H i).subgroupOf (F.L i)).Normal]

variable (hnilp : Group.IsNilpotent ↥((F.H i).subgroupOf (F.L i)))

variable (C : Subgroup ↥(F.L i))

variable (hFrob : OddOrder.Isaacs.Ch06.IsFrobeniusGroup
  ↥(F.L i) ((F.H i).subgroupOf (F.L i)) C)

theorem hypothesis78_weightedNuSum_inner_self_eq :
    ClassFunction.inner
      (F.hypothesis78 i hodd hnilp C hFrob).weightedNuSum
      (F.hypothesis78 i hodd hnilp C hFrob).weightedNuSum =
        (((((F.h i : ℝ) - 1) / (F.e i : ℝ)) : ℝ) : ℂ) := by sorry

end WeightedNorm

end FrobeniusFamily

end OddOrder.Peterfalvi.S09
