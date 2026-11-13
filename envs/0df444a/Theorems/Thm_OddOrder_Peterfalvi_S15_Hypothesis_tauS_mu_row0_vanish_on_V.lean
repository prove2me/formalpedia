-- Prove2me | Theorems.Thm_OddOrder_Peterfalvi_S15_Hypothesis_tauS_mu_row0_vanish_on_V
-- name    : OddOrder.Peterfalvi.S15.Hypothesis.tauS_mu_row0_vanish_on_V
-- status  : Proved
-- author  : @burkh4rt
-- created : 2026-11-12T16:03:22.210671+00:00
-- url     : https://prove2.me/theorems/5ba67039-5422-4c89-9e3f-1f1c7a0ded6c
-- title:
--   Prime-TI pin on $V$: the Dade image of $\mu_{0j}-\mu_{01}$ agrees with $\eta_{0j}-\eta_{01}$ on regular classes
-- statement:
--   Let $G$ be a finite group with `IsMinimalSimpleOdd G`, assume no maximal subgroup of $G$ is of type V, let `hyp : Hypothesis` be the Peterfalvi (13.1) configuration, and let $j<p$ with $j\ne0$. Let $\tau_S$ be the Dade isometry map attached to `hyp.dadeHypS0 hG` (with its full Dade isometry data), and write $\mu_{0j}$, $\eta_{0j}$ for the entries of row $0$ of the $\mu$- and $\eta$-grids. Then for every $x$ in the conjugacy saturation of $W\setminus(W_1\cup W_2)$,
--
--   $$\Big(\tau_S(\mu_{0j}-\mu_{01})-(\eta_{0j}-\eta_{01})\Big)(x)=0 .$$
--
--   This is the value identity on the regular classes $V^S$ coming from the prime-TI theory, used in the Section 13 analysis of the $\mu$-row $0$.
-- source:
--   Yawara Ishida, Lean 4 formalization of the Feit–Thompson (odd order) theorem, github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0), https://github.com/yawara/odd-order/blob/20a6fccbb63c0b138acda9f7fafd798c42f9441b/OddOrder/Peterfalvi/S15_HonestTypeP2A0.lean#L380-L460

import Definitions.Def_OddOrder_Peterfalvi_S15_SAndT_Setup_HypothesisBasics
import Definitions.Def_OddOrder_Peterfalvi_S15_SAndT_Setup_HypothesisSwap
import Definitions.Def_OddOrder_Peterfalvi_S15_SAndT_Setup_DegreesFirstSplit
import Definitions.Def_OddOrder_Peterfalvi_S15_SAndT_Setup_PairStructure
import Definitions.Def_OddOrder_Peterfalvi_S15_SAndT_Setup_CountingLayer
import Definitions.Def_OddOrder_Peterfalvi_S15_SAndT_Setup_Canonicalization
import Definitions.Def_OddOrder_Peterfalvi_S13_ElementaryAbelianKernel
import Definitions.Def_OddOrder_BG_Ch2_Uniqueness_S07_Theorem74
import Definitions.Def_OddOrder_Peterfalvi_S15_SAndT_Setup_TSideDegrees
import Definitions.Def_OddOrder_Peterfalvi_S10_TypePSupportA0
import Definitions.Def_OddOrder_Peterfalvi_S10_MinimalSimpleStructure
import Definitions.Def_OddOrder_Peterfalvi_S12_MaximalIII_IV_V_Core_Hypothesis
import Definitions.Def_OddOrder_Peterfalvi_S12_MaximalIII_IV_V_Core_CharacterParameters
import Definitions.Def_OddOrder_Peterfalvi_S12_MaximalIII_IV_V_Core_DadeCalculations
import Definitions.Def_OddOrder_GroupTheory_RepresentationTheory_PrimeTIResidue
import Definitions.Def_OddOrder_Peterfalvi_S10_StructureSetup
import Definitions.Def_OddOrder_BG_Ch4_FamilyOfMaximal_S15_MF_SetupLemma151
import Definitions.Def_OddOrder_Peterfalvi_S15_HonestTypeP2A0

namespace OddOrder.Peterfalvi.S15

open OddOrder.GroupTheory

variable {G : Type*} [Group G]

open scoped OddOrder.Peterfalvi.S12.FiniteInduce in

theorem Hypothesis.tauS_mu_row0_vanish_on_V [Fintype G] [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hnoV : ¬ ∃ M : Subgroup G, M ∈ maximalSubgroups G ∧ OddOrder.GroupTheory.IsTypeV M)
    (hyp : Hypothesis (G := G)) (j : Fin hyp.p)
    (hj0 : (j : ℕ) ≠ 0) :
    ∀ x ∈ conjClassSet ((hyp.W : Set G) \ ((hyp.W1 : Set G) ∪ (hyp.W2 : Set G))),
      (OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap (hyp.dadeHypS0 hG)
          ((hyp.dadeHypS0 hG).fullDadeIsometryData)
          (hyp.mu ⟨0, hyp.q_prime.pos⟩ j
            - hyp.mu ⟨0, hyp.q_prime.pos⟩ ⟨1, by have := hyp.three_le_p; omega⟩)
        - (hyp.eta ⟨0, hyp.q_prime.pos⟩ j
            - hyp.eta ⟨0, hyp.q_prime.pos⟩ ⟨1, by have := hyp.three_le_p; omega⟩)) x = 0 := by sorry

end OddOrder.Peterfalvi.S15
