-- Prove2me | Theorems.Thm_OddOrder_Peterfalvi_S09_FrobeniusFamily_hypothesis78_zetaNuRhoNormSq_ge_at
-- name    : OddOrder.Peterfalvi.S09.FrobeniusFamily.hypothesis78_zetaNuRhoNormSq_ge_at
-- status  : Proved
-- author  : @burkh4rt
-- created : 2026-11-12T08:28:33.665189+00:00
-- url     : https://prove2.me/theorems/577f52b0-2c71-4845-b0cc-d971e96286ff
-- title:
--   Peterfalvi (7.8.b): $1-e/h\le\|\zeta_0^{\nu\rho}\|^2$ for the local Frobenius datum
-- statement:
--   Let $G$ be a finite group of odd order, and let $F$ be a Frobenius family in $G$ (`FrobeniusFamily G k`): subgroups $L_j,H_j\le G$ ($j<k$, $k\ge 2$) with $H_j\le L_j$, each $L_j$ a Frobenius group with kernel $H_j$, $L_j=N_G(H_j)$, $H_j^\#$ a TI-subset with normalizer $L_j$, and the orders $|H_j|$ pairwise coprime. Fix a member $i<k$, assume the kernel $H_i$ (as a subgroup of $L_i$) is nilpotent, and let $C\le L_i$ be a subgroup with `IsFrobeniusGroup L_i H_i C` (a Frobenius complement). These data determine the canonical Peterfalvi (7.8) coherence datum $\mathcal H=$ `F.hypothesis78 i hodd hnilp C hFrob`, with fields such as `hyp76.zeta`, `ind1H`, `zetaDistinct`, `nu`, `beta`, `delta`.
--
--   For the canonical datum $\mathcal H=$ `localH78 F i …`,
--   $$1-\frac{\texttt{complementIndex}}{\texttt{kernelOrder}}\ \le\ \texttt{zetaNuRhoNormSq},$$
--   where `complementIndex` and `kernelOrder` are the quantities $e$ and $h$ of $\mathcal H$ (cast to $\mathbb R$) and `zetaNuRhoNormSq` is the squared norm of the $\rho$-image of the distinguished coherent character.
--
--   This is Peterfalvi (7.8.b) in its canonical local form for a Frobenius-family member.
--
--   **Formalization Note.** The ambient `Fintype`/`Invertible (Nat.card · : ℂ)` instances for $G$, $L_i$ and the kernel, and the normality instance for the kernel in $L_i$, are explicit hypotheses; they are automatic mathematically. Oddness of $|G|$ is the hypothesis `hodd : Odd (Nat.card G)`.
-- source:
--   Yawara Ishida, Lean 4 formalization of the Feit–Thompson (odd order) theorem, github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0), https://github.com/yawara/odd-order/blob/20a6fccbb63c0b138acda9f7fafd798c42f9441b/OddOrder/Peterfalvi/S09_FrobeniusSelectedEstimate.lean#L51-L183

import Definitions.Def_OddOrder_Peterfalvi_S09_FrobeniusGammaNormEstimate
import Definitions.Def_OddOrder_Peterfalvi_S09_NonexistenceCertain_FrobeniusFamily
import Definitions.Def_OddOrder_Peterfalvi_S09_FrobeniusSelectedEstimate

namespace OddOrder.Peterfalvi.S09

open OddOrder.RepresentationTheory

namespace FrobeniusFamily

variable {G : Type*} [Group G] {k : ℕ}

section LocalSelectedEstimate

variable [Fintype G] [Invertible (Nat.card G : ℂ)]

variable (F : FrobeniusFamily G k) (i : Fin k) (hodd : Odd (Nat.card G))

variable [Fintype ↥(F.L i)] [Invertible (Nat.card ↥(F.L i) : ℂ)]

variable [Invertible (Nat.card ↥((F.H i).subgroupOf (F.L i)) : ℂ)]

variable [((F.H i).subgroupOf (F.L i)).Normal]

variable (hnilp : Group.IsNilpotent ↥((F.H i).subgroupOf (F.L i)))

variable (C : Subgroup ↥(F.L i))

variable (hFrob : OddOrder.Isaacs.Ch06.IsFrobeniusGroup
  ↥(F.L i) ((F.H i).subgroupOf (F.L i)) C)

theorem hypothesis78_zetaNuRhoNormSq_ge_at :
    1 - ((localH78_S09_FrobeniusSelectedEstimate F i hodd hnilp C hFrob).complementIndex : ℝ) /
        ((localH78_S09_FrobeniusSelectedEstimate F i hodd hnilp C hFrob).kernelOrder : ℝ) ≤
      (localH78_S09_FrobeniusSelectedEstimate F i hodd hnilp C hFrob).zetaNuRhoNormSq := by sorry

end LocalSelectedEstimate

end FrobeniusFamily

end OddOrder.Peterfalvi.S09
