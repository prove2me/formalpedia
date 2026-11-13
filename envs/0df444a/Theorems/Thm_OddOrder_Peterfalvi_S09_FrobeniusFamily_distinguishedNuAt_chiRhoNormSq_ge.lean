-- Prove2me | Theorems.Thm_OddOrder_Peterfalvi_S09_FrobeniusFamily_distinguishedNuAt_chiRhoNormSq_ge
-- name    : OddOrder.Peterfalvi.S09.FrobeniusFamily.distinguishedNuAt_chiRhoNormSq_ge
-- status  : Proved
-- author  : @burkh4rt
-- created : 2026-11-12T08:29:05.976508+00:00
-- url     : https://prove2.me/theorems/b50e1dca-7236-407d-b098-5fb874a389a0
-- title:
--   Peterfalvi (7.8.b): $1-e_i/h_i\le\|(\nu\zeta^{(i)}_0)^{\rho_i}\|^2$ for the distinguished image
-- statement:
--   Let $G$ be a finite group of odd order, and let $F$ be a Frobenius family in $G$ (`FrobeniusFamily G k`): subgroups $L_j,H_j\le G$ ($j<k$, $k\ge 2$) with $H_j\le L_j$, each $L_j$ a Frobenius group with kernel $H_j$, $L_j=N_G(H_j)$, $H_j^\#$ a TI-subset with normalizer $L_j$, and the orders $|H_j|$ pairwise coprime. For every $j<k$ assume the kernel $H_j$ is nilpotent and that $C_j\le L_j$ is a Frobenius complement (`IsFrobeniusGroup L_j H_j (C j)`); the canonical (7.8) data of each member are then defined.
--
--   For every $i<k$,
--   $$1-\frac{e_i}{h_i}\ \le\ \texttt{chiRhoNormSq}\big(N_i\big)\ i ,$$
--   where $h_i=|H_i|$, $e_i=|L_i:H_i|$, $N_i=$ `distinguishedNuAt i`, and `chiRhoNormSq` of `F.familyHypothesis71` is the $\rho_i$-norm squared.
--
--   This is the family consumer form of Peterfalvi (7.8.b).
--
--   **Formalization Note.** The ambient `Fintype`/`Invertible (Nat.card · : ℂ)` instances for $G$, $L_i$ and the kernel, and the normality instance for the kernel in $L_i$, are explicit hypotheses; they are automatic mathematically. Oddness of $|G|$ is the hypothesis `hodd : Odd (Nat.card G)`.
-- source:
--   Yawara Ishida, Lean 4 formalization of the Feit–Thompson (odd order) theorem, github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0), https://github.com/yawara/odd-order/blob/20a6fccbb63c0b138acda9f7fafd798c42f9441b/OddOrder/Peterfalvi/S09_FrobeniusSelectedEstimate.lean#L197-L234

import Definitions.Def_OddOrder_Peterfalvi_S09_FrobeniusGammaNormEstimate
import Definitions.Def_OddOrder_Peterfalvi_S09_NonexistenceCertain_FrobeniusFamily
import Definitions.Def_OddOrder_Peterfalvi_S09_FrobeniusSelectedEstimate

namespace OddOrder.Peterfalvi.S09

open OddOrder.RepresentationTheory

namespace FrobeniusFamily

variable {G : Type*} [Group G] {k : ℕ}

section FamilySelectedEstimate

variable [Fintype G] [Invertible (Nat.card G : ℂ)]

variable (F : FrobeniusFamily G k) (hodd : Odd (Nat.card G))

variable (hnilp : ∀ j : Fin k,
  Group.IsNilpotent ↥((F.H j).subgroupOf (F.L j)))

variable (C : ∀ j : Fin k, Subgroup ↥(F.L j))

variable (hFrob : ∀ j : Fin k, OddOrder.Isaacs.Ch06.IsFrobeniusGroup
  ↥(F.L j) ((F.H j).subgroupOf (F.L j)) (C j))

theorem distinguishedNuAt_chiRhoNormSq_ge (i : Fin k) :
    (1 : ℝ) - (F.e i : ℝ) / (F.h i : ℝ) ≤
      (F.familyHypothesis71).chiRhoNormSq
        (F.distinguishedNuAt hodd hnilp C hFrob i) i := by sorry

end FamilySelectedEstimate

end FrobeniusFamily

end OddOrder.Peterfalvi.S09
