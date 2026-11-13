-- Prove2me | Theorems.Thm_OddOrder_Peterfalvi_S09_FrobeniusFamily_hypothesis78_beta_conj_sub
-- name    : OddOrder.Peterfalvi.S09.FrobeniusFamily.hypothesis78_beta_conj_sub
-- status  : Proved
-- author  : @burkh4rt
-- created : 2026-11-12T08:22:56.958613+00:00
-- url     : https://prove2.me/theorems/027ff4d7-35b1-4444-8425-49101d603d49
-- title:
--   Peterfalvi (7.9): $\bar\beta-\beta=\nu\zeta-\nu\bar\zeta$ for the Frobenius (7.8) datum
-- statement:
--   Let $G$ be a finite group of odd order, and let $F$ be a Frobenius family in $G$ (`FrobeniusFamily G k`): subgroups $L_j,H_j\le G$ ($j<k$, $k\ge 2$) with $H_j\le L_j$, each $L_j$ a Frobenius group with kernel $H_j$, $L_j=N_G(H_j)$, $H_j^\#$ a TI-subset with normalizer $L_j$, and the orders $|H_j|$ pairwise coprime. Fix a member $i<k$, assume the kernel $H_i$ (as a subgroup of $L_i$) is nilpotent, and let $C\le L_i$ be a subgroup with `IsFrobeniusGroup L_i H_i C` (a Frobenius complement). These data determine the canonical Peterfalvi (7.8) coherence datum $\mathcal H=$ `F.hypothesis78 i hodd hnilp C hFrob`, with fields such as `hyp76.zeta`, `ind1H`, `zetaDistinct`, `nu`, `beta`, `delta`.
--
--   Let $\zeta=\zeta_{\mathrm{zetaDistinct}}$. Then
--   $$\overline{\beta}-\beta\;=\;\nu(\zeta)-\nu(\overline{\zeta}),$$
--   with $\beta=$ `beta` and $\nu=$ `nu` the coherent extension of $\mathcal H$.
--
--   This is the Frobenius input `hbeta_conj_sub` to the realness of $\Delta$ in Peterfalvi (7.9).
--
--   **Formalization Note.** The ambient `Fintype`/`Invertible (Nat.card · : ℂ)` instances for $G$, $L_i$ and the kernel, and the normality instance for the kernel in $L_i$, are explicit hypotheses; they are automatic mathematically. Oddness of $|G|$ is the hypothesis `hodd : Odd (Nat.card G)`.
-- source:
--   Yawara Ishida, Lean 4 formalization of the Feit–Thompson (odd order) theorem, github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0), https://github.com/yawara/odd-order/blob/20a6fccbb63c0b138acda9f7fafd798c42f9441b/OddOrder/Peterfalvi/S09_FrobeniusConjIndex.lean#L344-L448

import Definitions.Def_OddOrder_Peterfalvi_S09_CrossOrthogonality
import Definitions.Def_OddOrder_Peterfalvi_S09_FrobeniusHypothesis79
import Definitions.Def_OddOrder_GroupTheory_RepresentationTheory_CharacterProduct
import Definitions.Def_OddOrder_GroupTheory_RepresentationTheory_BrauerPermutationUnconditional
import Definitions.Def_OddOrder_Peterfalvi_S09_FrobeniusEstimate
import Definitions.Def_OddOrder_GroupTheory_RepresentationTheory_CliffordDecomposition
import Definitions.Def_OddOrder_Peterfalvi_S09_FrobeniusConjIndex

namespace OddOrder.Peterfalvi.S09

open OddOrder.RepresentationTheory

namespace FrobeniusFamily

variable {G : Type*} [Group G] {k : ℕ}

open OddOrder.Peterfalvi.S09.Cert in

theorem hypothesis78_beta_conj_sub [Fintype G] [Invertible (Nat.card G : ℂ)]
    (F : FrobeniusFamily G k) (i : Fin k) (hodd : Odd (Nat.card G))
    [Fintype ↥(F.L i)] [Invertible (Nat.card ↥(F.L i) : ℂ)]
    [Invertible (Nat.card ↥((F.H i).subgroupOf (F.L i)) : ℂ)]
    [((F.H i).subgroupOf (F.L i)).Normal]
    (hnilp : Group.IsNilpotent ↥((F.H i).subgroupOf (F.L i)))
    (C : Subgroup ↥(F.L i))
    (hFrob : OddOrder.Isaacs.Ch06.IsFrobeniusGroup ↥(F.L i) ((F.H i).subgroupOf (F.L i)) C) :
    (F.hypothesis78 i hodd hnilp C hFrob).beta.conj
        - (F.hypothesis78 i hodd hnilp C hFrob).beta
      = (F.hypothesis78 i hodd hnilp C hFrob).nu
          ((F.hypothesis78 i hodd hnilp C hFrob).hyp76.zeta
            (F.hypothesis78 i hodd hnilp C hFrob).zetaDistinct)
        - (F.hypothesis78 i hodd hnilp C hFrob).nu
          ((F.hypothesis78 i hodd hnilp C hFrob).hyp76.zeta
            (F.hypothesis78 i hodd hnilp C hFrob).zetaDistinct).conj := by sorry

end FrobeniusFamily

end OddOrder.Peterfalvi.S09
