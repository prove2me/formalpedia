-- Prove2me | Theorems.Thm_OddOrder_Peterfalvi_S09_FrobeniusFamily_hypothesis79_zeta_cross_eq_zero_at
-- name    : OddOrder.Peterfalvi.S09.FrobeniusFamily.hypothesis79_zeta_cross_eq_zero_at
-- status  : Proved
-- author  : @burkh4rt
-- created : 2026-11-12T08:23:34.373189+00:00
-- url     : https://prove2.me/theorems/0d97e0d5-9351-44f3-86cd-dfa4f87f4a28
-- title:
--   Peterfalvi (7.9)/(7.10): coherent images from distinct Frobenius families are orthogonal
-- statement:
--   Let $G$ be a finite group of odd order, and let $F$ be a Frobenius family in $G$ (`FrobeniusFamily G k`): subgroups $L_j,H_j\le G$ ($j<k$, $k\ge 2$) with $H_j\le L_j$, each $L_j$ a Frobenius group with kernel $H_j$, $L_j=N_G(H_j)$, $H_j^\#$ a TI-subset with normalizer $L_j$, and the orders $|H_j|$ pairwise coprime. Let $i\ne j$ be two members of the Frobenius family; each satisfies the hypotheses of the local setup (kernel $H_i$, $H_j$ nilpotent, Frobenius complements $C_i,C_j$ with `IsFrobeniusGroup`), giving canonical (7.8) data $\mathcal H_i,\mathcal H_j$.
--
--   Let $r$ be an index of the $i$-th family different from `ind1H`, and $s$ an index of the $j$-th family different from `ind1H`. Then
--   $$\big\langle \nu_i(\zeta^{(i)}_r),\ \nu_j(\zeta^{(j)}_s)\big\rangle=0 ,$$
--   where $\zeta^{(m)}_t=$ `hyp76.zeta t` and $\nu_m=$ `nu` of $\mathcal H_m$.
--
--   This extends the pairwise orthogonality of Peterfalvi (7.9) from the distinguished characters to all non-principal members of two different families, as needed for the (7.10) Gamma decomposition.
--
--   **Formalization Note.** The ambient `Fintype`/`Invertible (Nat.card · : ℂ)` instances for $G$, $L_i$ and the kernel, and the normality instance for the kernel in $L_i$, are explicit hypotheses; they are automatic mathematically. Oddness of $|G|$ is the hypothesis `hodd : Odd (Nat.card G)`.
-- source:
--   Yawara Ishida, Lean 4 formalization of the Feit–Thompson (odd order) theorem, github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0), https://github.com/yawara/odd-order/blob/20a6fccbb63c0b138acda9f7fafd798c42f9441b/OddOrder/Peterfalvi/S09_FrobeniusFamilyOrthogonality.lean#L324-L404

import Definitions.Def_OddOrder_Peterfalvi_S09_FrobeniusConjIndex

namespace OddOrder.Peterfalvi.S09

open OddOrder.RepresentationTheory

namespace FrobeniusFamily

variable {G : Type*} [Group G] {k : ℕ}

section CrossFamily

variable [Fintype G] [Invertible (Nat.card G : ℂ)]

variable (F : FrobeniusFamily G k) {i j : Fin k}

variable (hodd : Odd (Nat.card G))

variable [Fintype ↥(F.L i)] [Invertible (Nat.card ↥(F.L i) : ℂ)]

variable [Invertible (Nat.card ↥((F.H i).subgroupOf (F.L i)) : ℂ)]

variable [((F.H i).subgroupOf (F.L i)).Normal]

variable (hnilp_i : Group.IsNilpotent ↥((F.H i).subgroupOf (F.L i)))

variable (C_i : Subgroup ↥(F.L i))

variable (hFrob_i : OddOrder.Isaacs.Ch06.IsFrobeniusGroup
  ↥(F.L i) ((F.H i).subgroupOf (F.L i)) C_i)

variable [Fintype ↥(F.L j)] [Invertible (Nat.card ↥(F.L j) : ℂ)]

variable [Invertible (Nat.card ↥((F.H j).subgroupOf (F.L j)) : ℂ)]

variable [((F.H j).subgroupOf (F.L j)).Normal]

variable (hnilp_j : Group.IsNilpotent ↥((F.H j).subgroupOf (F.L j)))

variable (C_j : Subgroup ↥(F.L j))

variable (hFrob_j : OddOrder.Isaacs.Ch06.IsFrobeniusGroup
  ↥(F.L j) ((F.H j).subgroupOf (F.L j)) C_j)

theorem hypothesis79_zeta_cross_eq_zero_at (hij : i ≠ j)
    {r : Fin ((F.hypothesis78 i hodd hnilp_i C_i hFrob_i).hyp76.n + 1)}
    (hr : r ≠ (F.hypothesis78 i hodd hnilp_i C_i hFrob_i).ind1H)
    {s : Fin ((F.hypothesis78 j hodd hnilp_j C_j hFrob_j).hyp76.n + 1)}
    (hs : s ≠ (F.hypothesis78 j hodd hnilp_j C_j hFrob_j).ind1H) :
    ClassFunction.inner
      ((F.hypothesis78 i hodd hnilp_i C_i hFrob_i).nu
        ((F.hypothesis78 i hodd hnilp_i C_i hFrob_i).hyp76.zeta r))
      ((F.hypothesis78 j hodd hnilp_j C_j hFrob_j).nu
        ((F.hypothesis78 j hodd hnilp_j C_j hFrob_j).hyp76.zeta s)) = 0 := by sorry

end CrossFamily

end FrobeniusFamily

end OddOrder.Peterfalvi.S09
