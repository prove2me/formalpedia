-- Prove2me | Theorems.Thm_GenCountSampleLLL_insertion_return_probability_unit_interval
-- name    : GenCountSampleLLL.insertion_return_probability_unit_interval
-- status  : Open
-- author  : @wcysai
-- created : 2026-11-13T05:52:34.644202+00:00
-- url     : https://prove2.me/theorems/d84a6e51-1878-4dcb-a2a9-469aca20f8a1
-- title:
--   Conditional return probability lies in [0,1]
-- statement:
--   For a valid corridor label $e=(T,z)$, the expected reciprocal list size of the pinned list satisfies $0\le\operatorname{retProb}(e)\le1$. The pinned list always contains $e$, so its cardinality is at least one. This bounds the forward-layer transition probabilities in Algorithm 3.
-- source:
--   Jain, Mizgerd, Pham, A general counting and sampling Lovász local lemma, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/702.pdf, Algorithm 3 and proof of Lemma 6.4, pp.20 and 23.

import Definitions.Def_GenCountSampleLLL_insertionChain
noncomputable section
open scoped Classical BigOperators ENNReal

namespace GenCountSampleLLL
theorem insertion_return_probability_unit_interval (I : Inst) (D : Finset (Fin I.m)) (a : Fin I.m)
    (T : Finset (Fin I.m)) (z : I.Assign)
    (hT : T ∈ I.twoTrees D a) (hz : z ∈ I.labelsE D a T) :
    0 ≤ I.retProb D a (T,z) ∧ I.retProb D a (T,z) ≤ 1 := by sorry
end GenCountSampleLLL
