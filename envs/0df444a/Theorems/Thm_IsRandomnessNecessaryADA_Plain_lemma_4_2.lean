-- Prove2me | Theorems.Thm_IsRandomnessNecessaryADA_Plain_lemma_4_2
-- name    : IsRandomnessNecessaryADA.Plain.lemma_4_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T10:20:41.154866+00:00
-- url     : https://prove2.me/theorems/60d1b82b-4035-48d7-bcfd-fcaee9a3518c
-- title:
--   Lemma 4.2 — selected-query density
-- statement:
--   Let $N,M,L$ be finite dimensions with $L\le N$. Fix locations $r\in[M]^N$ and support patterns $v^0,\ldots,v^L$. Let the full tables $(Q_0,\ldots,Q_L)$ and the selected index $J\in\{0,\ldots,L\}$ have any joint distribution such that $Q_\ell\sim\mu_{r,v^\ell}$ for every $\ell$. For every set $A$ of tables,
--   $$\Pr[Q_J\in A]\le (N+1)2^N\mu(A).$$
--   The selection may depend on the entire table sequence and additional randomness; no independence is assumed. The claim also applies to a law conditional on any fixed past transcript for which these marginals hold: such a conditional law is one of the arbitrary joint laws quantified here. This density estimate remains valid even when a profile coupling fails, and is the source's control on adaptively selected queries.
--
--   Differences from the source:
--   - encoding: one-based finite sets and ordered datasets → Fin indices and function tuples, with full real answers; reason: reindexing preserves every query, ordered sample with repetition, and response
--   - encoding: arbitrary selection J, including whole-sequence dependence and conditioning on fixed past transcripts → an arbitrary joint PMF on the table sequence together with the selected index; reason: this represents both randomized selection and each conditional joint law having the required marginals
--   - generalization: Section 4 uses N=20n>0 and positive M → all natural N and M admitting the locations r, including the empty-row boundary; reason: the union bound uses only L≤N and the completion marginals; the source is obtained by its positive dimensions
-- source:
--   Edith Cohen, Haim Kaplan, Yishay Mansour, Shay Sapir, Uri Stemmer, Eliad Tsfadia, STOC 2027 submission #267 (October 2026), Lemma 4.2 and Eq.(5), p.13; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/267.pdf; PDF/printed pages coincide.

import Definitions.Def_IsRandomnessNecessaryADA_Plain_Tables

set_option autoImplicit false

namespace IsRandomnessNecessaryADA.Plain

/-- Lemma 4.2 and Eq.(5), p.13. An arbitrary joint law includes randomized selection
and any law conditional on a fixed positive-probability transcript with these marginals. -/
theorem lemma_4_2 (N M L : ℕ) (hL : L ≤ N)
    (r : Locations N M) (v : Fin (L + 1) → BooleanQuery (Fin N))
    (joint : PMF ((Fin (L + 1) → Table N M) × Fin (L + 1)))
    (marginals : ∀ j, joint.map (fun w => w.1 j) = completionLaw r (v j))
    (A : Set (Table N M)) :
    probability (joint.map (fun w => w.1 w.2)) A ≤
      (densityFactor N : ℝ) * probability (tableLaw N M) A := by sorry

end IsRandomnessNecessaryADA.Plain
