-- Prove2me | Theorems.Thm_OddOrder_Peterfalvi_S09_FrobeniusFamily_hypothesis78_coherence_agreement_at
-- name    : OddOrder.Peterfalvi.S09.FrobeniusFamily.hypothesis78_coherence_agreement_at
-- status  : Proved
-- author  : @burkh4rt
-- created : 2026-11-12T08:28:45.275225+00:00
-- url     : https://prove2.me/theorems/350d8796-674b-48aa-96cd-1e711f0d5a21
-- title:
--   Peterfalvi (7.8): coherent extension agrees with the Dade map on degree-zero source differences
-- statement:
--   Let $G$ be a finite group of odd order, and let $F$ be a Frobenius family in $G$ (`FrobeniusFamily G k`): subgroups $L_j,H_j\le G$ ($j<k$, $k\ge 2$) with $H_j\le L_j$, each $L_j$ a Frobenius group with kernel $H_j$, $L_j=N_G(H_j)$, $H_j^\#$ a TI-subset with normalizer $L_j$, and the orders $|H_j|$ pairwise coprime. Fix a member $i<k$, assume the kernel $H_i$ (as a subgroup of $L_i$) is nilpotent, and let $C\le L_i$ be a subgroup with `IsFrobeniusGroup L_i H_i C` (a Frobenius complement). These data determine the canonical Peterfalvi (7.8) coherence datum $\mathcal H=$ `F.hypothesis78 i hodd hnilp C hFrob`, with fields such as `hyp76.zeta`, `ind1H`, `zetaDistinct`, `nu`, `beta`, `delta`.
--
--   Let $\mathcal H=$ `localH78 F i …`, $\tau=$ `hyp76.hyp71.τ` the Dade isometry, and $r\ne$ `ind1H`. Then
--   $$\tau\big(\zeta_r-d_r\,\zeta_0\big)=\nu(\zeta_r)-d_r\,\nu(\zeta_0),$$
--   where $\zeta_t=$ `hyp76.zeta t`, $d_r=$ `hyp76.d r`, and the argument of $\tau$ is the degree-zero source difference (with its support proof `psi_support r`).
--
--   This is the coherence/agreement property of the concrete extension $\nu$ with the Dade map on the family members.
--
--   **Formalization Note.** The ambient `Fintype`/`Invertible (Nat.card · : ℂ)` instances for $G$, $L_i$ and the kernel, and the normality instance for the kernel in $L_i$, are explicit hypotheses; they are automatic mathematically. Oddness of $|G|$ is the hypothesis `hodd : Odd (Nat.card G)`.
-- source:
--   Yawara Ishida, Lean 4 formalization of the Feit–Thompson (odd order) theorem, github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0), https://github.com/yawara/odd-order/blob/20a6fccbb63c0b138acda9f7fafd798c42f9441b/OddOrder/Peterfalvi/S09_FrobeniusGammaDecomposition.lean#L127-L191

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

theorem hypothesis78_coherence_agreement_at
    {r : Fin ((localH78_S09_FrobeniusGammaDecomposition F i hodd hnilp C hFrob).hyp76.n + 1)}
    (hr : r ≠ (localH78_S09_FrobeniusGammaDecomposition F i hodd hnilp C hFrob).ind1H) :
    (localH78_S09_FrobeniusGammaDecomposition F i hodd hnilp C hFrob).hyp76.hyp71.τ
        ⟨(localH78_S09_FrobeniusGammaDecomposition F i hodd hnilp C hFrob).hyp76.zeta r -
            (localH78_S09_FrobeniusGammaDecomposition F i hodd hnilp C hFrob).hyp76.d r •
              (localH78_S09_FrobeniusGammaDecomposition F i hodd hnilp C hFrob).hyp76.zeta 0,
          (localH78_S09_FrobeniusGammaDecomposition F i hodd hnilp C hFrob).hyp76.psi_support r⟩ =
      (localH78_S09_FrobeniusGammaDecomposition F i hodd hnilp C hFrob).nu
          ((localH78_S09_FrobeniusGammaDecomposition F i hodd hnilp C hFrob).hyp76.zeta r) -
        (localH78_S09_FrobeniusGammaDecomposition F i hodd hnilp C hFrob).hyp76.d r •
          (localH78_S09_FrobeniusGammaDecomposition F i hodd hnilp C hFrob).nu
            ((localH78_S09_FrobeniusGammaDecomposition F i hodd hnilp C hFrob).hyp76.zeta 0) := by sorry

end LocalCoefficient

end FrobeniusFamily

end OddOrder.Peterfalvi.S09
