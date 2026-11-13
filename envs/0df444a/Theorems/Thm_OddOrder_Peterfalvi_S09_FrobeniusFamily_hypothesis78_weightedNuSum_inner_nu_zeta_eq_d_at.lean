-- Prove2me | Theorems.Thm_OddOrder_Peterfalvi_S09_FrobeniusFamily_hypothesis78_weightedNuSum_inner_nu_zeta_eq_d_at
-- name    : OddOrder.Peterfalvi.S09.FrobeniusFamily.hypothesis78_weightedNuSum_inner_nu_zeta_eq_d_at
-- status  : Proved
-- author  : @burkh4rt
-- created : 2026-11-12T08:25:59.401287+00:00
-- url     : https://prove2.me/theorems/b78fa2f7-861a-442c-a63a-b706d635dd7d
-- title:
--   Peterfalvi (7.8)/(7.10): the weighted coherent sum projects onto $\nu(\zeta_r)$ with coefficient $d_r$
-- statement:
--   Let $G$ be a finite group of odd order, and let $F$ be a Frobenius family in $G$ (`FrobeniusFamily G k`): subgroups $L_j,H_j\le G$ ($j<k$, $k\ge 2$) with $H_j\le L_j$, each $L_j$ a Frobenius group with kernel $H_j$, $L_j=N_G(H_j)$, $H_j^\#$ a TI-subset with normalizer $L_j$, and the orders $|H_j|$ pairwise coprime. Fix a member $i<k$, assume the kernel $H_i$ (as a subgroup of $L_i$) is nilpotent, and let $C\le L_i$ be a subgroup with `IsFrobeniusGroup L_i H_i C` (a Frobenius complement). These data determine the canonical Peterfalvi (7.8) coherence datum $\mathcal H=$ `F.hypothesis78 i hodd hnilp C hFrob`, with fields such as `hyp76.zeta`, `ind1H`, `zetaDistinct`, `nu`, `beta`, `delta`.
--
--   Let $\mathcal H=$ `localH78 F i …` be the canonical (7.8) datum of member $i$, $W=$ `weightedNuSum`, and let $r\ne$ `ind1H`. Then
--   $$\langle W,\ \nu(\zeta_r)\rangle=d_r,$$
--   where $d_r=$ `hyp76.d r`.
--
--   This computes the coefficients of the weighted coherent sum against the non-principal source images.
--
--   **Formalization Note.** The ambient `Fintype`/`Invertible (Nat.card · : ℂ)` instances for $G$, $L_i$ and the kernel, and the normality instance for the kernel in $L_i$, are explicit hypotheses; they are automatic mathematically. Oddness of $|G|$ is the hypothesis `hodd : Odd (Nat.card G)`.
-- source:
--   Yawara Ishida, Lean 4 formalization of the Feit–Thompson (odd order) theorem, github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0), https://github.com/yawara/odd-order/blob/20a6fccbb63c0b138acda9f7fafd798c42f9441b/OddOrder/Peterfalvi/S09_FrobeniusGammaDecomposition.lean#L85-L125

import Definitions.Def_OddOrder_Peterfalvi_S09_FrobeniusConjIndex
import Definitions.Def_OddOrder_GroupTheory_RepresentationTheory_BrauerPermutationUnconditional
import Definitions.Def_OddOrder_Peterfalvi_S08_CoherenceCorePart1
import Definitions.Def_OddOrder_Peterfalvi_S09_FrobeniusGammaDecomposition

namespace OddOrder.Peterfalvi.S09

open OddOrder.RepresentationTheory

namespace FrobeniusFamily

variable {G : Type*} [Group G] {k : ℕ}

section LocalCoefficient

variable [Fintype G] [Invertible (Nat.card G : ℂ)]

variable (F : FrobeniusFamily G k) (i : Fin k) (hodd : Odd (Nat.card G))

variable [Fintype ↥(F.L i)] [Invertible (Nat.card ↥(F.L i) : ℂ)]

variable [Fintype ↥((F.H i).subgroupOf (F.L i))]

variable [Invertible (Nat.card ↥((F.H i).subgroupOf (F.L i)) : ℂ)]

variable [((F.H i).subgroupOf (F.L i)).Normal]

variable (hnilp : Group.IsNilpotent ↥((F.H i).subgroupOf (F.L i)))

variable (C : Subgroup ↥(F.L i))

variable (hFrob : OddOrder.Isaacs.Ch06.IsFrobeniusGroup
  ↥(F.L i) ((F.H i).subgroupOf (F.L i)) C)

omit [Fintype ↥((F.H i).subgroupOf (F.L i))] in

theorem hypothesis78_weightedNuSum_inner_nu_zeta_eq_d_at
    {r : Fin ((localH78_S09_FrobeniusGammaDecomposition F i hodd hnilp C hFrob).hyp76.n + 1)}
    (hr : r ≠ (localH78_S09_FrobeniusGammaDecomposition F i hodd hnilp C hFrob).ind1H) :
    ClassFunction.inner
        (localH78_S09_FrobeniusGammaDecomposition F i hodd hnilp C hFrob).weightedNuSum
        ((localH78_S09_FrobeniusGammaDecomposition F i hodd hnilp C hFrob).nu
          ((localH78_S09_FrobeniusGammaDecomposition F i hodd hnilp C hFrob).hyp76.zeta r)) =
      (localH78_S09_FrobeniusGammaDecomposition F i hodd hnilp C hFrob).hyp76.d r := by sorry

end LocalCoefficient

end FrobeniusFamily

end OddOrder.Peterfalvi.S09
