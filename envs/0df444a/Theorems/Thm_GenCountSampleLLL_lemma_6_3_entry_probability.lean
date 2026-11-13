-- Prove2me | Theorems.Thm_GenCountSampleLLL_lemma_6_3_entry_probability
-- name    : GenCountSampleLLL.lemma_6_3_entry_probability
-- status  : Proved
-- author  : @wcysai
-- created : 2026-11-13T05:18:51.231898+00:00
-- url     : https://prove2.me/theorems/acc051a1-7a29-4ea3-9083-66d7ee500b5c
-- title:
--   Lemma 6.3: a list entry appears with its product probability
-- statement:
--   Let $T\in\mathcal T_{D,a}$ be a rooted 2-tree, $z\in E_T$ an assignment on $U_T$, and $e=(T,z)$. Then the random list $L$ contains $e$ with probability exactly $\nu_{U_T}(z)$. This is the first assertion of Lemma 6.3; it does not include the conditional-law assertion.
-- source:
--   Jain, Mizgerd, Pham, A general counting and sampling Lovász local lemma, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/702.pdf, Lemma 6.3, p.22.

import Definitions.Def_GenCountSampleLLL_twoTrees
noncomputable section
open scoped Classical BigOperators ENNReal

namespace GenCountSampleLLL
theorem lemma_6_3_entry_probability (I : Inst) (D : Finset (Fin I.m)) (a : Fin I.m)
    (T : Finset (Fin I.m)) (z : I.Assign)
    (hT : T ∈ I.twoTrees D a) (hz : z ∈ I.labelsE D a T) :
    (∑ ω : I.ExpSpace, (I.expLaw ω).toReal *
      (if (T,z) ∈ I.Llist D a ω then (1 : ℝ) else 0)) = I.nuU (I.UT D T) z := by sorry
end GenCountSampleLLL
