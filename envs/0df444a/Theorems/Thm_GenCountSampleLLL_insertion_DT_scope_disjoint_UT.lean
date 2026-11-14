-- Prove2me | Theorems.Thm_GenCountSampleLLL_insertion_DT_scope_disjoint_UT
-- name    : GenCountSampleLLL.insertion_DT_scope_disjoint_UT
-- status  : Proved
-- author  : @wcysai
-- created : 2026-11-13T06:05:18.76106+00:00
-- url     : https://prove2.me/theorems/76a68b8c-af87-4b5d-aa13-93e2dfeeba57
-- title:
--   Far constraints use no resampled variables
-- statement:
--   For every $b\in D_T=D\setminus N_D^2[T]$, its variable scope is disjoint from $U_T=\operatorname{vbl}(N_D[T])$. Consequently resampling $U_T$ preserves the constraints of $D_T$.
-- source:
--   Jain, Mizgerd, Pham, A general counting and sampling Lovász local lemma, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/702.pdf, §6.2 and proof of Lemma 6.4, pp.22–23.

import Definitions.Def_GenCountSampleLLL_insertionChain
noncomputable section
open scoped Classical BigOperators ENNReal

namespace GenCountSampleLLL
theorem insertion_DT_scope_disjoint_UT (I : Inst) (D T : Finset (Fin I.m))
    (b : Fin I.m) (hb : b ∈ I.DT D T) : Disjoint (I.vbl b) (I.UT D T) := by sorry
end GenCountSampleLLL
