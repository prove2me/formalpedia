-- Prove2me | Theorems.Thm_OddOrder_Peterfalvi_S09_FrobeniusFamily_exists_weightedGammaDecomposition
-- name    : OddOrder.Peterfalvi.S09.FrobeniusFamily.exists_weightedGammaDecomposition
-- status  : Proved
-- author  : @burkh4rt
-- created : 2026-11-12T08:25:15.200843+00:00
-- url     : https://prove2.me/theorems/b2ee7120-bb87-4f41-a5c7-b1893ca510b8
-- title:
--   Peterfalvi (7.10): weighted Gamma decomposition over a family of Frobenius subgroups
-- statement:
--   Let $G$ be a finite group of odd order, and let $F$ be a Frobenius family in $G$ (`FrobeniusFamily G k`): subgroups $L_j,H_j\le G$ ($j<k$, $k\ge 2$) with $H_j\le L_j$, each $L_j$ a Frobenius group with kernel $H_j$, $L_j=N_G(H_j)$, $H_j^\#$ a TI-subset with normalizer $L_j$, and the orders $|H_j|$ pairwise coprime. For every $j<k$ assume the kernel $H_j$ is nilpotent and that $C_j\le L_j$ is a Frobenius complement (`IsFrobeniusGroup L_j H_j (C j)`); the canonical (7.8) data of each member are then defined.
--
--   Write $\beta_i=$ `betaAt i`, $\Gamma_i=$ `gammaAt i`, $N_j=$ `distinguishedNuAt j`, $W_j=$ `weightedNuSumAt j`, $w_j=(h_j-1)/e_j$ (`BsumWeight j`), where $h_j=|H_j|$, $e_j=|L_j:H_j|$. Let $i<k$ and let $B\subseteq\{0,\dots,k-1\}$ be a finite set with $j\neq i$ for all $j\in B$. Then there exist integers $x_j$ ($j<k$) and a class function $\Gamma_1$ on $G$ such that:
--
--   1. $\langle\beta_i,N_j\rangle=x_j$ for all $j$;
--   2. $\langle W_j,W_l\rangle=w_j$ if $j=l$ and $0$ otherwise, for $j,l\in B$;
--   3. $\displaystyle \Gamma_i=\sum_{j\in B}x_j\,W_j+\Gamma_1$;
--   4. $\langle\Gamma_1,W_j\rangle=0$ for all $j\in B$.
--
--   This is the family-wide decomposition of the Gamma residual in Peterfalvi (7.10).
--
--   **Formalization Note.** The ambient `Fintype`/`Invertible (Nat.card · : ℂ)` instances for $G$, $L_i$ and the kernel, and the normality instance for the kernel in $L_i$, are explicit hypotheses; they are automatic mathematically. Oddness of $|G|$ is the hypothesis `hodd : Odd (Nat.card G)`.
-- source:
--   Yawara Ishida, Lean 4 formalization of the Feit–Thompson (odd order) theorem, github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0), https://github.com/yawara/odd-order/blob/20a6fccbb63c0b138acda9f7fafd798c42f9441b/OddOrder/Peterfalvi/S09_FrobeniusGammaDecomposition.lean#L639-L785

import Definitions.Def_OddOrder_Peterfalvi_S09_FrobeniusConjIndex
import Definitions.Def_OddOrder_GroupTheory_RepresentationTheory_BrauerPermutationUnconditional
import Definitions.Def_OddOrder_Peterfalvi_S08_CoherenceCorePart1
import Definitions.Def_OddOrder_Peterfalvi_S09_FrobeniusGammaDecomposition

namespace OddOrder.Peterfalvi.S09

open OddOrder.RepresentationTheory

namespace FrobeniusFamily

variable {G : Type*} [Group G] {k : ℕ}

section FamilyRealization

variable [Fintype G] [Invertible (Nat.card G : ℂ)]

variable (F : FrobeniusFamily G k) (hodd : Odd (Nat.card G))

variable (hnilp : ∀ j : Fin k,
  Group.IsNilpotent ↥((F.H j).subgroupOf (F.L j)))

variable (C : ∀ j : Fin k, Subgroup ↥(F.L j))

variable (hFrob : ∀ j : Fin k, OddOrder.Isaacs.Ch06.IsFrobeniusGroup
  ↥(F.L j) ((F.H j).subgroupOf (F.L j)) (C j))

theorem exists_weightedGammaDecomposition
    (i : Fin k) (B : Finset (Fin k))
    (hB : ∀ j ∈ B, i ≠ j) :
    ∃ x : Fin k → ℤ, ∃ Γ₁ : ClassFunction G ℂ,
      (∀ j, ClassFunction.inner
        (F.betaAt hodd hnilp C hFrob i)
        (F.distinguishedNuAt hodd hnilp C hFrob j) = (x j : ℂ)) ∧
      (∀ j ∈ B, ∀ l ∈ B,
        ClassFunction.inner
          (F.weightedNuSumAt hodd hnilp C hFrob j)
          (F.weightedNuSumAt hodd hnilp C hFrob l) =
            if j = l then (F.BsumWeight j : ℂ) else 0) ∧
      F.gammaAt hodd hnilp C hFrob i =
        (∑ j ∈ B,
          (((x j : ℝ) : ℂ) • F.weightedNuSumAt hodd hnilp C hFrob j)) + Γ₁ ∧
      ∀ j ∈ B, ClassFunction.inner Γ₁
        (F.weightedNuSumAt hodd hnilp C hFrob j) = 0 := by sorry

end FamilyRealization

end FrobeniusFamily

end OddOrder.Peterfalvi.S09
