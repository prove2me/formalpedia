-- Prove2me | Theorems.Thm_GenCountSampleLLL_lemma_6_3_list_expectation
-- name    : GenCountSampleLLL.lemma_6_3_list_expectation
-- status  : Proved
-- author  : @wcysai
-- created : 2026-11-13T05:40:17.9472+00:00
-- url     : https://prove2.me/theorems/9ecbc074-6e54-4970-86f6-3e0b8578a846
-- title:
--   Pinned list conditional expectation identity
-- statement:
--   For a valid list entry $e=(T,z)$, write $q_e=\nu_{U_T}(z)$. For every real-valued function $\phi$ of the list, $\mathbb E[\mathbf 1_{e\in L}\phi(L)] = q_e\mathbb E[\phi(L_e)]$. This is the test-function form of the conditional-law assertion in Lemma 6.3.
-- source:
--   Jain, Mizgerd, Pham, A general counting and sampling Lovász local lemma, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/702.pdf, Lemma 6.3 and proof of Lemma 6.4, pp.22–23.

import Definitions.Def_GenCountSampleLLL_insertionChain
noncomputable section
open scoped Classical BigOperators

namespace GenCountSampleLLL
theorem lemma_6_3_list_expectation (I : Inst) (D : Finset (Fin I.m)) (a : Fin I.m)
    (T : Finset (Fin I.m)) (z : I.Assign)
    (hT : T ∈ I.twoTrees D a) (hz : z ∈ I.labelsE D a T)
    (φ : Finset (Finset (Fin I.m) × I.Assign) → ℝ) :
    (∑ ω : I.ExpSpace, (I.expLaw ω).toReal *
      (if (T,z) ∈ I.Llist D a ω then φ (I.Llist D a ω) else 0)) =
      I.nuU (I.UT D T) z *
      ∑ ω : I.ExpSpace, (I.expLaw ω).toReal * φ (I.Le D a (T,z) ω) := by sorry
end GenCountSampleLLL
