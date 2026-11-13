-- Prove2me | Theorems.Thm_GenCountSampleLLL_insertion_auxiliary_stochastic
-- name    : GenCountSampleLLL.insertion_auxiliary_stochastic
-- status  : Open
-- author  : @wcysai
-- created : 2026-11-13T05:45:57.967574+00:00
-- url     : https://prove2.me/theorems/6de9102a-ff65-4273-a4c5-afd384ec2edc
-- title:
--   The auxiliary insertion kernel is stochastic
-- statement:
--   Under the standing local-lemma hypothesis and $a\in D$, the auxiliary insertion matrix $P_{D,a}$ is a stochastic matrix on the recursively defined state space: every entry is nonnegative and each row sums to one. This is the well-definedness obligation for the auxiliary chain used in Lemma 6.4.
-- source:
--   Jain, Mizgerd, Pham, A general counting and sampling Lovász local lemma, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/702.pdf, §5.1–5.2 and Algorithm 3, pp.17–20.

import Definitions.Def_GenCountSampleLLL_insertionChain
import Definitions.Def_mm_basic
noncomputable section
open scoped Classical BigOperators ENNReal

namespace GenCountSampleLLL
theorem insertion_auxiliary_stochastic (I : Inst) (x : Fin I.m → ℝ) (hx : ∀ b, 0 < x b ∧ x b < 1)
    (hLLL : I.LLLCond (1 / 100) x) (D : Finset (Fin I.m)) (a : Fin I.m) (ha : a ∈ D) :
    MarkovMixing.IsStochastic (I.Pker D a) := by sorry
end GenCountSampleLLL
