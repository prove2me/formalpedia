-- Prove2me | Theorems.Thm_GenCountSampleLLL_piDist_isDist_of_good
-- name    : GenCountSampleLLL.piDist_isDist_of_good
-- status  : Proved
-- author  : @wcysai
-- created : 2026-11-13T05:42:16.969261+00:00
-- url     : https://prove2.me/theorems/8dcf4485-8194-4fd9-a201-16592f6aff56
-- title:
--   Insertion-chain weights normalize to a distribution
-- statement:
--   For the insertion chain with $a\in D$, suppose the input subinstance $D\setminus\{a\}$ has a satisfying assignment and $\beta>0$. Then the normalized weights $\pi(X)=\widetilde w(X)/M$ form a probability distribution. This proves the normalization step needed in Lemma 6.4; satisfiability is implied by the paper’s standing local-lemma hypothesis.
-- source:
--   Jain, Mizgerd, Pham, A general counting and sampling Lovász local lemma, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/702.pdf, Lemma 6.4 and proof, pp.22–23.

import Definitions.Def_GenCountSampleLLL_insertionChain
import Definitions.Def_mm_basic
noncomputable section
open scoped Classical BigOperators ENNReal

namespace GenCountSampleLLL
theorem piDist_isDist_of_good (I : Inst) (D : Finset (Fin I.m)) (a : Fin I.m)
    (ha : a ∈ D) (β : ℝ) (hβ : 0 < β)
    (hgood : (I.Good (D.erase a)).Nonempty) : MarkovMixing.IsDist (I.piDist β D a) := by sorry
end GenCountSampleLLL
