-- Prove2me | Theorems.Thm_GenCountSampleLLL_insertion_auxiliary_weighted_balance
-- name    : GenCountSampleLLL.insertion_auxiliary_weighted_balance
-- status  : Open
-- author  : @wcysai
-- created : 2026-11-13T05:45:54.084547+00:00
-- url     : https://prove2.me/theorems/31cf53d5-21a9-42b0-a774-d244aa1c9801
-- title:
--   The auxiliary insertion kernel satisfies weighted detailed balance
-- statement:
--   Under the standing local-lemma hypothesis and $a\in D$, the unnormalized weights of the auxiliary insertion chain satisfy $w(X)P(X,Y)=w(Y)P(Y,X)$ for every pair of states. This is the inductive edge-by-edge balance assertion proved at the start of Lemma 6.4; the independently proved return-edge identity handles its random-list contribution.
-- source:
--   Jain, Mizgerd, Pham, A general counting and sampling Lovász local lemma, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/702.pdf, proof of Lemma 6.4, p.23.

import Definitions.Def_GenCountSampleLLL_insertionChain
import Definitions.Def_mm_basic
noncomputable section
open scoped Classical BigOperators ENNReal

namespace GenCountSampleLLL
theorem insertion_auxiliary_weighted_balance (I : Inst) (x : Fin I.m → ℝ) (hx : ∀ b, 0 < x b ∧ x b < 1)
    (hLLL : I.LLLCond (1 / 100) x) (D : Finset (Fin I.m)) (a : Fin I.m) (ha : a ∈ D) :
    ∀ X Y : I.S D a, I.w D a X * I.Pker D a X Y = I.w D a Y * I.Pker D a Y X := by sorry
end GenCountSampleLLL
