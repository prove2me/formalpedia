-- Prove2me | Theorems.Thm_OddOrder_Peterfalvi_S16_pair_cross_orthogonal
-- name    : OddOrder.Peterfalvi.S16.pair_cross_orthogonal
-- status  : Proved
-- author  : @burkh4rt
-- created : 2026-11-12T15:27:51.245192+00:00
-- url     : https://prove2.me/theorems/79b71d16-1358-469b-8eab-ce8b8d2d9054
-- title:
--   Peterfalvi (4.1): family-wide cross-orthogonality $\langle\nu(\varphi_i),\nu(\chi_j)\rangle=0$
-- statement:
--   Let $G$ be a finite group which is minimal simple odd-order (`hG`), and let $L,M$ be non-conjugate maximal subgroups of $G$ (`¬ IsConjugateSubgroup L M`) with (7.8) coherence data `dataL : TypeICoherent78Data L` and `dataM : TypeICoherent78Data M`. Let $i\in\{0,\dots,n_L\}$ with $i\ne$ `dataL.ind1H` and $j\in\{0,\dots,n_M\}$ with $j\neq$ `dataM.ind1H` (nontrivial family indices). Then
--   $$\bigl\langle\ \nu_L(\zeta^L_i),\ \nu_M(\zeta^M_j)\ \bigr\rangle \;=\; 0,$$
--   where $\nu_L=$ `(dataL.h78 hG).nu`, $\zeta^L_i=$ `(dataL.h78 hG).hyp76.zeta i`, and likewise for $M$.
--
--   This is the family-wide form of "$\mathcal{L}^{\tau_1}$ is orthogonal to $\mathcal{M}^{\tau_1}$": each member pairs with its conjugate (equal degree, distinct by odd order), the two $\nu$-differences are Dade images with disjoint supports, and orthonormality of virtual characters concludes.
-- source:
--   Yawara Ishida, Lean 4 formalization of the Feit–Thompson (odd order) theorem, github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0), https://github.com/yawara/odd-order/blob/20a6fccbb63c0b138acda9f7fafd798c42f9441b/OddOrder/Peterfalvi/S16_PairingCoherence.lean#L997-L1050

import Definitions.Def_OddOrder_Peterfalvi_S14_MaximalI_Hypothesis
import Definitions.Def_OddOrder_Peterfalvi_S14_MaximalI_RhoConstancy
import Definitions.Def_OddOrder_Peterfalvi_S14_MaximalI_PairCoherence
import Definitions.Def_OddOrder_Peterfalvi_S14_MaximalI_FrobeniusStructure
import Definitions.Def_OddOrder_Peterfalvi_S14_MaximalI_MinimalCounterexample
import Definitions.Def_OddOrder_Peterfalvi_S14_MaximalI_DadeContradiction
import Definitions.Def_OddOrder_Peterfalvi_S14_MaximalI_RhoMEvaluation
import Definitions.Def_OddOrder_Peterfalvi_S14_MaximalI_NormPackage
import Definitions.Def_OddOrder_Peterfalvi_S14_MaximalI_TypeICovering
import Definitions.Def_OddOrder_GroupTheory_RepresentationTheory_BrauerPermutationUnconditional
import Definitions.Def_OddOrder_Peterfalvi_S08_CoherenceCorePart1
import Definitions.Def_OddOrder_Peterfalvi_S09_FrobeniusConjIndex
import Definitions.Def_OddOrder_Peterfalvi_S09_CrossOrthogonality
import Definitions.Def_OddOrder_Peterfalvi_S09_FrobeniusHypothesis79
import Definitions.Def_OddOrder_GroupTheory_RepresentationTheory_CharacterProduct
import Definitions.Def_OddOrder_Peterfalvi_S16_PairingCoherence

namespace OddOrder.Peterfalvi.S16

open OddOrder.GroupTheory

open OddOrder.RepresentationTheory

open OddOrder.Peterfalvi.S09

open OddOrder.Peterfalvi.S09.Cert

open scoped OddOrder.Peterfalvi.S12.FiniteInduce

variable {G : Type*} [Group G]

section Pairing

variable [Finite G] {L M : Subgroup G}

variable (dataL : TypeICoherent78Data L) (dataM : TypeICoherent78Data M)

variable (hG : OddOrder.BG.IsMinimalSimpleOdd G)

theorem pair_cross_orthogonal
    (hL : L ∈ maximalSubgroups G) (hM : M ∈ maximalSubgroups G)
    (hnc : ¬ OddOrder.BG.Ch4.S14.IsConjugateSubgroup L M)
    {i : Fin (dataL.n + 1)} (hi : i ≠ dataL.ind1H)
    {j : Fin (dataM.n + 1)} (hj : j ≠ dataM.ind1H) :
    ClassFunction.inner ((dataL.h78 hG).nu ((dataL.h78 hG).hyp76.zeta i))
      ((dataM.h78 hG).nu ((dataM.h78 hG).hyp76.zeta j)) = 0 := by sorry

end Pairing

end OddOrder.Peterfalvi.S16
