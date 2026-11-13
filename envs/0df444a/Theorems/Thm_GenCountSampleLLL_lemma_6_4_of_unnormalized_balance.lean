-- Prove2me | Theorems.Thm_GenCountSampleLLL_lemma_6_4_of_unnormalized_balance
-- name    : GenCountSampleLLL.lemma_6_4_of_unnormalized_balance
-- status  : Proved
-- author  : @wcysai
-- created : 2026-11-13T05:42:20.357666+00:00
-- url     : https://prove2.me/theorems/93dc35eb-baef-4864-8cee-d3e5026a772e
-- title:
--   Stationarity and reversibility from unnormalized balance
-- statement:
--   Assume $a\in D$, $\beta>0$, the input subinstance is satisfiable, the insertion kernel $K$ is stochastic, and the unnormalized weights $\widetilde w$ satisfy detailed balance for $K$. Then their normalized version is a stationary and reversible probability distribution. This isolates the last step of the proof of Lemma 6.4.
-- source:
--   Jain, Mizgerd, Pham, A general counting and sampling Lovász local lemma, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/702.pdf, Lemma 6.4 and proof, pp.22–23.

import Definitions.Def_GenCountSampleLLL_insertionChain
import Definitions.Def_mm_basic
noncomputable section
open scoped Classical BigOperators ENNReal

namespace GenCountSampleLLL
theorem lemma_6_4_of_unnormalized_balance (I : Inst)
    (D : Finset (Fin I.m)) (a : Fin I.m) (ha : a ∈ D) (β : ℝ) (hβ : 0 < β)
    (hgood : (I.Good (D.erase a)).Nonempty)
    (hK : MarkovMixing.IsStochastic (I.Kker β D a))
    (hbalance : ∀ X Y : I.S D a,
      I.wtil β D a X * I.Kker β D a X Y = I.wtil β D a Y * I.Kker β D a Y X) :
    MarkovMixing.IsStationary (I.Kker β D a) (I.piDist β D a) ∧
      MarkovMixing.DetailedBalance (I.Kker β D a) (I.piDist β D a) := by sorry
end GenCountSampleLLL
