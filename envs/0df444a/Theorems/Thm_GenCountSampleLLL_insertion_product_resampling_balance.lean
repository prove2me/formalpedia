-- Prove2me | Theorems.Thm_GenCountSampleLLL_insertion_product_resampling_balance
-- name    : GenCountSampleLLL.insertion_product_resampling_balance
-- status  : Proved
-- author  : @wcysai
-- created : 2026-11-13T06:05:29.613241+00:00
-- url     : https://prove2.me/theorems/9c6c6fd7-6663-4b1f-b0d3-fbc24d2eb453
-- title:
--   Product-law resampling balance
-- statement:
--   For a product distribution, assignments $\sigma,\tau$, and a variable set $U$, one has $\nu(\sigma)\nu_U(\tau)=\nu_U(\sigma)\nu(\operatorname{merge}_U(\tau,\sigma))$. This is the weight identity used for the tree-to-layer resampling edge.
-- source:
--   Jain, Mizgerd, Pham, A general counting and sampling Lovász local lemma, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/702.pdf, §6.2 and proof of Lemma 6.4, pp.22–23.

import Definitions.Def_GenCountSampleLLL_insertionChain
noncomputable section
open scoped Classical BigOperators ENNReal

namespace GenCountSampleLLL
theorem insertion_product_resampling_balance (I : Inst) (U : Finset (Fin I.n)) (σ τ : I.Assign) :
    I.nuA σ * I.nuU U τ = I.nuU U σ * I.nuA (I.merge U τ σ) := by sorry
end GenCountSampleLLL
