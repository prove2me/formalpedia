-- Prove2me | Theorems.Thm_MatroidSensOracle_lemma_5_3
-- name    : MatroidSensOracle.lemma_5_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T16:50:50.051577+00:00
-- url     : https://prove2.me/theorems/9383842d-b3cc-4a2d-b6a7-faf595bd3753
-- title:
--   Lemma 5.3: if flows of value $\mathrm{val}(h)$ in $\mathcal G+U$ use at least $i$ buffer edges, then $\lambda_{G+U}=\lambda_G+f-i$
-- statement:
--   Let $G$ be an input graph, $s\ne t$, $f\ge0$, and $U=(I,F)$ an update set of $G$ with $F\subseteq E$ and $|U|\le f$. Let $\mathcal G+U$ be $G+U$ with $2f$ zero-cost parallel $(s,t)$ buffer edges. If $i$ is the least number of buffer edges carrying flow in an $(s,t)$-flow of value $f+\lambda_G(s,t)$ in $\mathcal G+U$, then
--   $$\lambda_{G+U}(s,t)=\lambda_G(s,t)+f-i.$$
--
--   The max-flow oracle finds $i$ by binary search over $[0,2f]$.
--
--   Differences from the source:
--   - reading: every (s, t)-flow of value val(h) in 𝒢 + U saturates a minimum of i parallel (s, t) edges → i is the least number of buffer edges carrying flow over all (s, t)-flows of value val(h) in 𝒢 + U; reason: the minimum over flows, as the proof uses it
--   - encoding: val(h); 𝒢 + U → f + λ_G(s, t) (as p.28 states); G + U followed by the 2f buffer edges; reason: U updates G only, so 𝒢 + U is G + U with the buffers
-- source:
--   Choudhary, Kumar, Saggi, Sensitivity Oracles for Matroid Packing, Matroid Covering, and Matching Problems with Applications, arXiv:2609.01283 (held version, sha256 0de50841…), Lemma 5.3, p.28 (PDF p.31), with the construction of 𝒢 on pp.27–28

import Mathlib
import Definitions.Def_MatroidSensOracle_InputGraph

set_option autoImplicit false

namespace MatroidSensOracle

/-- **Lemma 5.3.** Choudhary, Kumar, Saggi, arXiv:2609.01283 (held version, sha256 0de50841…), p.28
(PDF p.31): "For any update set U of size at most f, if every (s, t)-flow of value val(h) in 𝒢 + U
saturates a minimum of i parallel (s, t) edges, then λ_{G+U}(s, t) = λ_G(s, t) + f − i." Setting
(pp.27–28): "we augment G to a graph 𝒢 by adding 2f zero-cost parallel (s, t)-edges, and saturating
the first f of them in the preprocessed flow h (thus, value of flow h (denoted by val(h)) in 𝒢 is
equal to f + λ_G(s, t))."

**Formalization Note.** `G` is the simple input graph, `U = (I, F)` an update of `G` (`F ⊆ E`,
`|I| + |F| ≤ f`); `𝒢 + U` is `G + U` followed by the `2f` buffer edges (the update touches `G` only),
and `val(h) = f + λ_G(s, t)`. "Saturates a minimum of `i` parallel edges" is read as: `i` is the least
number of buffer edges carrying flow, over all `(s, t)`-flows of value `val(h)` in `𝒢 + U`. -/
theorem lemma_5_3 {n : ℕ} (G : InputGraph n) (s t : Fin n) (hst : s ≠ t) (f : ℕ) (U : Update n)
    (hU : U.del ⊆ G.E) (hf : U.size ≤ f) (i : ℕ)
    (hi : IsLeast {j : ℕ | ∃ g, ((G.plus U).addParallel s t (2 * f)).IsFlow s t g ∧
        ((G.plus U).addParallel s t (2 * f)).value s g = (f : ℤ) + G.toMultigraph.maxFlow s t ∧
        bufferUse ((G.plus U).addParallel s t (2 * f)) (G.plus U).m g = j} i) :
    ((G.plus U).maxFlow s t : ℤ) = G.toMultigraph.maxFlow s t + f - i := by sorry

end MatroidSensOracle
