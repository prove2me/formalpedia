-- Prove2me | Theorems.Thm_GenCountSampleLLL_lemma_6_4_return_balance
-- name    : GenCountSampleLLL.lemma_6_4_return_balance
-- status  : Proved
-- author  : @wcysai
-- created : 2026-11-13T05:40:11.432201+00:00
-- url     : https://prove2.me/theorems/29754c43-bcff-44f1-a4b0-181627debcd4
-- title:
--   Return-edge flow identity for the insertion chain
-- statement:
--   For a valid corridor label $e=(T,z)$, write $q_e=\nu_{U_T}(z)$. Let $\omega_e=\mathbb E[\mathbf1_{e\in L}/|L|]$, with the fraction interpreted as zero when the list is empty. Then $\omega_e=q_e\mathbb E[1/|L_e|]$. This is the random-list return-edge identity used to prove detailed balance in Lemma 6.4.
-- source:
--   Jain, Mizgerd, Pham, A general counting and sampling Lovász local lemma, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/702.pdf, Lemma 6.3 and proof of Lemma 6.4, pp.22–23.

import Definitions.Def_GenCountSampleLLL_insertionChain
noncomputable section
open scoped Classical BigOperators

namespace GenCountSampleLLL
theorem lemma_6_4_return_balance (I : Inst) (D : Finset (Fin I.m)) (a : Fin I.m)
    (T : Finset (Fin I.m)) (z : I.Assign)
    (hT : T ∈ I.twoTrees D a) (hz : z ∈ I.labelsE D a T) :
    I.expL D a (fun L => if (T,z) ∈ L then 1 / (L.card : ℝ) else 0) =
      I.nuU (I.UT D T) z * I.retProb D a (T,z) := by sorry
end GenCountSampleLLL
