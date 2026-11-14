-- Prove2me | Theorems.Thm_GenCountSampleLLL_insertion_tree_forward_stochastic
-- name    : GenCountSampleLLL.insertion_tree_forward_stochastic
-- status  : Proved
-- author  : @wcysai
-- created : 2026-11-13T06:04:30.665542+00:00
-- url     : https://prove2.me/theorems/657e85a3-dd9b-425c-8c8b-56c0cbb0c0ea
-- title:
--   The tree FORWARDS rule is stochastic
-- statement:
--   Let $a\in D$, $T\in\mathcal T_{D,a}$, and $\sigma\in E_T^*$. The FORWARDS rule at the tree state $T_T(\sigma)$ has nonnegative transition probabilities and total mass one on the recursively constructed state space. This is the resampling case of auxiliary-kernel stochasticity.
-- source:
--   Jain, Mizgerd, Pham, A general counting and sampling Lovász local lemma, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/702.pdf, Algorithm 3 and §6.2, pp.20 and 22.

import Definitions.Def_GenCountSampleLLL_insertionChain
noncomputable section
open scoped Classical BigOperators ENNReal

namespace GenCountSampleLLL
theorem insertion_tree_forward_stochastic (I : Inst) (D : Finset (Fin I.m)) (a : Fin I.m)
    (ha : a ∈ D) (T : Finset (Fin I.m)) (hT : T ∈ I.twoTrees D a)
    (σ : I.Assign) (hσ : σ ∈ I.Estar D a T) :
    (∀ Y : I.S D a, 0 ≤ I.baseRule D a (Inst.Base.tree T σ) Rule.fwd Y.1) ∧
      (∑ Y : I.S D a, I.baseRule D a (Inst.Base.tree T σ) Rule.fwd Y.1) = 1 := by sorry
end GenCountSampleLLL
