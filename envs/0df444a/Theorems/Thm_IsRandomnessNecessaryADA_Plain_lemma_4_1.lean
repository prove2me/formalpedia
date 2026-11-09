-- Prove2me | Theorems.Thm_IsRandomnessNecessaryADA_Plain_lemma_4_1
-- name    : IsRandomnessNecessaryADA.Plain.lemma_4_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T10:23:02.674484+00:00
-- url     : https://prove2.me/theorems/3724b8fb-e3b6-4c76-8823-db76aa537e74
-- title:
--   Lemma 4.1 — coupling a location-dependent threshold sequence
-- statement:
--   Fix positive $N,M$, a sample length $n$, any deterministic mechanism $m$ over $[N]\times[M]$, and a fixed list $h$ of past full query tables. Draw $R$ uniformly on $[M]^N$. For each $r$, choose any threshold path with common set $C(r)$ and an arbitrary ordering of its complement. Its length $L(r)=N-|C(r)|$ and all its choices may depend on $r$.
--
--   There is a joint-table sampling kernel $K_r$ for $Q_0,\ldots,Q_{L(r)}$ whose marginal at every $r,j$ is exactly $\mu_{r,v^j(r)}$, and whose simultaneous agreement satisfies
--   $$\Pr_{R,Q\sim K_R}\left[\forall\ell\le L(R),\ V_{i_\ell}^{h}(Q_{\ell-1})=V_{i_\ell}^{h}(Q_\ell)\right]\ge1-N2^{N-1}\sqrt{\frac{2N^n}{M}}.$$
--   Here $i_\ell$ is the distinct row changed at that step. Profiles include all $(N-1)^n$ ordered samples avoiding that row, with their own replayed histories. The marginals hold pointwise in the hidden locations even when the path depends on those locations. This provides the single-round full-table coupling used by the plain-model attack.
--
--   Differences from the source:
--   - encoding: one-based finite sets and ordered datasets → Fin indices and function tuples, with full real answers; reason: reindexing preserves every query, ordered sample with repetition, and response
--   - reading: N+1 threshold patterns, with Definition 3.2 allowing N−|C|+1 patterns → an R-dependent path of length L(R)=N−|C(R)|, with pointwise marginals at all its indices and the same N-based failure bound; reason: this includes the literal N-change case and every common-set path; each row changes at most once in the proof on pp.11–12
--   - generalization: Section 4 fixes N=20n and n>2 → any positive N and M and any natural sample length n; reason: the coupling proof uses only the row count and profile dimension; specializing N=20n recovers the full source setting
-- source:
--   Edith Cohen, Haim Kaplan, Yishay Mansour, Shay Sapir, Uri Stemmer, Eliad Tsfadia, STOC 2027 submission #267 (October 2026), Lemma 4.1 and Eq.(2), p.11; proof §§4.3–4.4, pp.11–12; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/267.pdf; PDF/printed pages coincide.

import Definitions.Def_IsRandomnessNecessaryADA_Plain_Tables

set_option autoImplicit false

namespace IsRandomnessNecessaryADA.Plain

attribute [local instance] Classical.propDecidable

/-- Lemma 4.1, p.11. Paths may depend arbitrarily on r, including their length.
The kernel marginals hold for every r, not merely after averaging locations. -/
theorem lemma_4_1 (N M n : ℕ) (hN : 0 < N) [NeZero M]
    (m : Mechanism (Fin N × Fin M) n) (h : List (Table N M))
    (path : Locations N M → ThresholdPath N) :
    ∃ K : (r : Locations N M) → PMF (Fin ((path r).length + 1) → Table N M),
      (∀ r j, (K r).map (fun Q => Q j) = completionLaw r (thresholdPattern (path r) j)) ∧
      1 - (N : ℝ) * (2 : ℝ) ^ (N - 1) * Real.sqrt (2 * (N : ℝ) ^ n / M) ≤
        probability
          ((PMF.uniformOfFintype (Locations N M)).bind (fun r =>
            (K r).map (fun Q => decide (profilesAgree m r h (path r) Q))))
          {true} := by sorry

end IsRandomnessNecessaryADA.Plain
