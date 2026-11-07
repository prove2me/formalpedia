-- Prove2me | Theorems.Thm_ImpatientMatching_lemma_4_9
-- name    : ImpatientMatching.lemma_4_9
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T05:52:17.833671+00:00
-- url     : https://prove2.me/theorems/a4cf707d-1448-4b79-8baf-3a454a9eaeaf
-- title:
--   Lemma 4.9 — edge-customer backlog
-- statement:
--   On the Finite-Finite construction, let $U$ be a set of $K$ vertices, $o(e)\in e\cap U$ an endpoint of each edge, and $\nu_U$ the invariant law of the cover rule. Then
--   $$\sum_{e\in E_H}\mathbb E_{\nu_U}Q^c_e\le n\left(\frac{\varepsilon}{8(L+1)}-\sigma\right),$$
--   where $Q^c_e$ is the number of waiting customers of type $c_e$.
--
--   This bounds the customers lost to waiting among the edge types.
--
--   Differences from the source:
--   - generalization: the standing assumption n ≥ n₀ of the reduction → no such hypothesis; reason: the proof does not use (11); on n ≥ n₀ this is the source's statement
--   - reading: νU, the invariant law of Lemma B.1 → every invariant law of the cover rule; reason: Lemma B.1 makes it unique
--   - encoding: fresh randomization → one Exp(1) coin per event, in a private coordinate of the seed space; reason: any randomization over the countable decision set is a measurable function of it
-- source:
--   C. Yan and S. M. Varma, Impatience Makes Matching NP-Hard, manuscript (sha256 7b1051b6c661435675185b0663cb08ab217698a2c4ee07fa0f473686dbb6bed9), Lemma 4.9, (23), p.16

import Definitions.Def_ImpatientMatching_Construction

open scoped ENNReal
open NSWApxHard.Reduction DynStochMatching.Reward

namespace ImpatientMatching

/-- **Lemma 4.9 (edge-customer backlog).** Yan–Varma, manuscript (sha256 7b1051b6…), (23), p.16:
`Σ_e E_{ν_U} Q^c_e ≤ n(ε/(8(L + 1)) − σ)`, for the invariant law `ν_U` of the cover rule.

**Formalization Note.** The hypothesis `n ≥ n₀` is not needed here: the proof does not use (11). -/
theorem lemma_4_9 (H : GraphInput) (K : ℕ) (hH : IsSourceRange H K)
    (U : Finset (Fin H.N)) (o : Fin (edgeCount H) → Fin H.N) (hU : U.card = K)
    (ho : IsCoverAssignment H U o) (ν : State (H.N + (edgeCount H + 1)) → ℝ)
    (hν : IsInvariantLaw (ffInstance H K) (coverRule U o) ν) :
    ∑ e : Fin (edgeCount H), nuMean ν (fun q => (q (edgeIdx e) : ℝ≥0∞)) ≤
      ENNReal.ofReal ((H.N : ℝ) * ((eps : ℝ) / (8 * ((LFF : ℝ) + 1)) - (sigmaFF : ℝ))) := by sorry

end ImpatientMatching
