-- Prove2me | Theorems.Thm_OddOrder_Peterfalvi_S09_FrobeniusFamily_exists_conjIndex_hypothesis78
-- name    : OddOrder.Peterfalvi.S09.FrobeniusFamily.exists_conjIndex_hypothesis78
-- status  : Proved
-- author  : @burkh4rt
-- created : 2026-11-12T08:22:53.081441+00:00
-- url     : https://prove2.me/theorems/1ed4550c-310b-4a0b-a5fc-cfbc17667f0f
-- title:
--   Peterfalvi (7.9): the distinguished $\zeta$ has a conjugate in the family at a distinct index
-- statement:
--   Let $G$ be a finite group of odd order, and let $F$ be a Frobenius family in $G$ (`FrobeniusFamily G k`): subgroups $L_j,H_j\le G$ ($j<k$, $k\ge 2$) with $H_j\le L_j$, each $L_j$ a Frobenius group with kernel $H_j$, $L_j=N_G(H_j)$, $H_j^\#$ a TI-subset with normalizer $L_j$, and the orders $|H_j|$ pairwise coprime. Fix a member $i<k$, assume the kernel $H_i$ (as a subgroup of $L_i$) is nilpotent, and let $C\le L_i$ be a subgroup with `IsFrobeniusGroup L_i H_i C` (a Frobenius complement). These data determine the canonical Peterfalvi (7.8) coherence datum $\mathcal H=$ `F.hypothesis78 i hodd hnilp C hFrob`, with fields such as `hyp76.zeta`, `ind1H`, `zetaDistinct`, `nu`, `beta`, `delta`.
--
--   Writing $\zeta_j=$ `hyp76.zeta j` for the characters of the family, there is an index $j_1\ne$ `ind1H` with
--   $$\zeta_{j_1}=\overline{\zeta_{\mathrm{zetaDistinct}}} .$$
--
--   This supplies the conjugate-index data for the cross-orthogonality in Peterfalvi (7.9).
--
--   **Formalization Note.** The ambient `Fintype`/`Invertible (Nat.card · : ℂ)` instances for $G$, $L_i$ and the kernel, and the normality instance for the kernel in $L_i$, are explicit hypotheses; they are automatic mathematically. Oddness of $|G|$ is the hypothesis `hodd : Odd (Nat.card G)`.
-- source:
--   Yawara Ishida, Lean 4 formalization of the Feit–Thompson (odd order) theorem, github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0), https://github.com/yawara/odd-order/blob/20a6fccbb63c0b138acda9f7fafd798c42f9441b/OddOrder/Peterfalvi/S09_FrobeniusConjIndex.lean#L79-L144

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

theorem exists_conjIndex_hypothesis78 [Fintype G] [Invertible (Nat.card G : ℂ)]
    (F : FrobeniusFamily G k) (i : Fin k) (hodd : Odd (Nat.card G))
    [Fintype ↥(F.L i)] [Invertible (Nat.card ↥(F.L i) : ℂ)]
    [Invertible (Nat.card ↥((F.H i).subgroupOf (F.L i)) : ℂ)]
    [((F.H i).subgroupOf (F.L i)).Normal]
    (hnilp : Group.IsNilpotent ↥((F.H i).subgroupOf (F.L i)))
    (C : Subgroup ↥(F.L i))
    (hFrob : OddOrder.Isaacs.Ch06.IsFrobeniusGroup ↥(F.L i) ((F.H i).subgroupOf (F.L i)) C) :
    ∃ j₁, j₁ ≠ (F.hypothesis78 i hodd hnilp C hFrob).ind1H ∧
      (F.hypothesis78 i hodd hnilp C hFrob).hyp76.zeta j₁
        = ((F.hypothesis78 i hodd hnilp C hFrob).hyp76.zeta
            (F.hypothesis78 i hodd hnilp C hFrob).zetaDistinct).conj := by sorry

end FrobeniusFamily

end OddOrder.Peterfalvi.S09
