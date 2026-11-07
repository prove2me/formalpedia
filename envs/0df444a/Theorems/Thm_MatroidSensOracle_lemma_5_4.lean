-- Prove2me | Theorems.Thm_MatroidSensOracle_lemma_5_4
-- name    : MatroidSensOracle.lemma_5_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T16:51:15.495191+00:00
-- url     : https://prove2.me/theorems/c4eadca2-fdd8-42fc-8ec3-e877a11649e3
-- title:
--   Lemma 5.4: $h$ is repairable in $\mathcal G+U$ iff $\lambda_{\mathcal G^*}(s^*,t^*)=|F_h|$, and then the min repaired cost is $c_{\mathcal G}(h)+c_{\mathcal G^*}(s^*,t^*)-\sum_{F_h}c(e)$
-- statement:
--   Let $G$ be an input graph, $s\ne t$, $f\ge0$, $\mathcal G$ the buffered graph ($G$ with $2f$ zero-cost $(s,t)$-edges), $h$ an $(s,t)$-flow of $\mathcal G$, and $U=(I,F)$ an update of $\mathcal G$ ($F$ any set of edges of $\mathcal G$, $I$ a list of new edges). Let $F_h=\{e\in F:h(e)=1\}$, $d=|F_h|$, and $\mathcal G^*=\mathcal G^*_h+\mathcal U^*$.
--
--   1. $\mathcal G+U$ has an $(s,t)$-flow of value $\mathrm{val}(h)$ if and only if $\lambda_{\mathcal G^*}(s^*,t^*)=d$.
--   2. In that case the minimum cost of an $(s,t)$-flow of value $\mathrm{val}(h)$ in $\mathcal G+U$ equals
--   $$c_{\mathcal G}(h)+c_{\mathcal G^*}(s^*,t^*)-\sum_{e\in F_h}c(e),$$
--   where $c_{\mathcal G^*}(s^*,t^*)$ is the minimum cost of an $(s^*,t^*)$-flow of value $d$ in $\mathcal G^*$.
--
--   It turns each test of the oracles of Theorem 5.5 into an $(s^*,t^*)$-flow query on $\mathcal G^*_h$ with $O(f)$ updates.
--
--   Differences from the source:
--   - generalization: h the precomputed min-cost (s, t)-max-flow of 𝒢 (saturating the first f buffer edges) → any (s, t)-flow h of 𝒢; reason: the proof uses only that h is a flow; the paper's h is a special case
--   - reading: U = (I, F) a set of updates → F any set of edges of 𝒢 (buffer edges included), I any list of new edges; reason: the max-flow oracle applies the lemma to U′ = (I, F ∪ {e_{i+1}, …, e_{2f}}) (p.29)
--   - reading: h can be repaired into a valid flow h′ in 𝒢 + U; c_𝒢∗(s∗, t∗) → an (s, t)-flow of 𝒢 + U of value val(h); the minimum cost of an (s∗, t∗)-flow of value d in 𝒢∗ (cycles allowed); reason: the use of the lemma on pp.29–30
--   - encoding: c(h′) = … for the minimum cost repaired flow → an identity in ℤ ∪ {+∞} between minimum costs, stated when the max-flow equals d; reason: then both sides are finite
--   - encoding: F∗ = (F \ F_h) ∪ {e_rev : e ∈ F_h}; {(s∗, x), (y, t∗) : (x, y) ∈ F_h} → the residual index set F; one new zero-cost edge (s∗, x) and one (y, t∗) per member of F_h; reason: residual edge e stands for e or e_rev; one pair of edges per member is how the proof routes d units
-- source:
--   Choudhary, Kumar, Saggi, Sensitivity Oracles for Matroid Packing, Matroid Covering, and Matching Problems with Applications, arXiv:2609.01283 (held version, sha256 0de50841…), Lemma 5.4, p.28 (PDF p.31); 𝒢∗_h, 𝒰∗, 𝒢∗ on p.28; c_𝒢∗ as used on p.30

import Mathlib
import Definitions.Def_MatroidSensOracle_InputGraph

set_option autoImplicit false

namespace MatroidSensOracle

/-- **Lemma 5.4.** Choudhary, Kumar, Saggi, arXiv:2609.01283 (held version, sha256 0de50841…), p.28
(PDF p.31): "Let U = (I, F) be a set of updates, and write d := |F_h|. The flow h in 𝒢 can be
repaired into a valid flow h′ in 𝒢 + U if and only if the (s∗, t∗)-max-flow in 𝒢∗ equals d. Moreover,
the minimum cost of any such repaired flow satisfies c(h′) = c_𝒢(h) + c_𝒢∗(s∗, t∗) − Σ_{e∈F_h} c(e)."

**Formalization Note.**
* `𝒢 = buffered G s t f` (the input graph with `2f` zero-cost `(s, t)`-buffer edges); `h` is any
  `(s, t)`-flow of `𝒢` (the paper's `h` is its precomputed min-cost max-flow; the statement holds for
  every flow). `U = (I, F)` is any update of `𝒢`: `F` a set of edges of `𝒢` (buffer edges included,
  as the max-flow oracle uses), `I` a list of new edges. `F_h = {e ∈ F : h(e) = 1}`, `d = |F_h|`.
* `𝒢∗ = starGraph 𝒢 h I F` (see `InputGraph`), with source `s∗` and sink `t∗`; in `𝒢∗` the vertices
  `s`, `t` are ordinary vertices.
* "Repaired into a valid flow `h′` in `𝒢 + U`": an `(s, t)`-flow of `𝒢 + U` with the value of `h`.
  `c_𝒢∗(s∗, t∗)` is the minimum cost of an `(s∗, t∗)`-flow of value `d` in `𝒢∗` (cycles allowed), and
  the identity is between minimum costs, stated when the max-flow equals `d`. -/
theorem lemma_5_4 {n : ℕ} (G : InputGraph n) (s t : Fin n) (hst : s ≠ t) (f : ℕ)
    (h : Fin (G.buffered s t f).m → Bool) (hh : (G.buffered s t f).IsFlow s t h)
    (I : List (Fin n × Fin n × ℤ)) (F : Finset (Fin (G.buffered s t f).m)) :
    ((∃ h', ((G.buffered s t f).apply I F).IsFlow s t h' ∧
        ((G.buffered s t f).apply I F).value s h' = (G.buffered s t f).value s h) ↔
      (starGraph (G.buffered s t f) h I F).maxFlow (sStar n) (tStar n) = (F.filter fun e => h e = true).card) ∧
    ((starGraph (G.buffered s t f) h I F).maxFlow (sStar n) (tStar n) = (F.filter fun e => h e = true).card →
      ((G.buffered s t f).apply I F).minCostFlow s t ((G.buffered s t f).value s h) =
        (((G.buffered s t f).flowCost h - ∑ e ∈ F.filter (fun e => h e = true), (G.buffered s t f).cost e : ℤ) :
            WithTop ℤ) +
          (starGraph (G.buffered s t f) h I F).minCostFlow (sStar n) (tStar n)
            ((F.filter fun e => h e = true).card : ℤ)) := by sorry

end MatroidSensOracle
