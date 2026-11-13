-- Prove2me | Theorems.Thm_GenCountSampleLLL_insertion_corridor_last_family
-- name    : GenCountSampleLLL.insertion_corridor_last_family
-- status  : Proved
-- author  : @wcysai
-- created : 2026-11-13T05:53:16.357148+00:00
-- url     : https://prove2.me/theorems/abe55202-3372-4255-8163-ba6ab6428bb5
-- title:
--   The last corridor layer has the input constraint family
-- statement:
--   For every rooted 2-tree $T\in\mathcal T_{D,a}$, the constraint family at the final corridor layer satisfies $D_{T,\ell(T)}=D\setminus\{a\}$. Hence every input assignment is eligible to label the final layer. This identity is used in the construction of the insertion chain.
-- source:
--   Jain, Mizgerd, Pham, A general counting and sampling Lovász local lemma, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/702.pdf, §2.1 and §5.1, pp.10 and 18.

import Definitions.Def_GenCountSampleLLL_twoTrees
noncomputable section
open scoped Classical BigOperators

namespace GenCountSampleLLL
theorem insertion_corridor_last_family (I : Inst) (D : Finset (Fin I.m)) (a : Fin I.m)
    (T : Finset (Fin I.m)) (hT : T ∈ I.twoTrees D a) :
    I.DTi D a T (I.ell D a T) = D.erase a := by sorry
end GenCountSampleLLL
