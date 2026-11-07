-- Prove2me | Theorems.Thm_ImpatientMatching_lemma_4_10
-- name    : ImpatientMatching.lemma_4_10
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T05:52:24.993722+00:00
-- url     : https://prove2.me/theorems/e3ab8bf9-bbad-4723-886a-8a9188b61f25
-- title:
--   Lemma 4.10 — flexible-customer backlog
-- statement:
--   On the Finite-Finite construction with $n\ge n_0=6\cdot10^{13}$, let $U$ be a set of $K$ vertices, $o(e)\in e\cap U$ an endpoint of each edge, and $\nu_U$ the invariant law of the cover rule. Then
--   $$\mathbb E_{\nu_U}Q^c_0\le\frac{\sigma n}{2},$$
--   where $Q^c_0$ is the number of waiting flexible customers.
--
--   Together with Lemma 4.9 this gives the lower threshold $g_+$ of the value gap.
--
--   Differences from the source:
--   - reading: νU, the invariant law of Lemma B.1 → every invariant law of the cover rule; reason: Lemma B.1 makes it unique
--   - encoding: fresh randomization → one Exp(1) coin per event, in a private coordinate of the seed space; reason: any randomization over the countable decision set is a measurable function of it
-- source:
--   C. Yan and S. M. Varma, Impatience Makes Matching NP-Hard, manuscript (sha256 7b1051b6c661435675185b0663cb08ab217698a2c4ee07fa0f473686dbb6bed9), Lemma 4.10, (24), p.16

import Definitions.Def_ImpatientMatching_Construction

open scoped ENNReal
open NSWApxHard.Reduction DynStochMatching.Reward

namespace ImpatientMatching

/-- **Lemma 4.10 (flexible-customer backlog).** Yan–Varma, manuscript (sha256 7b1051b6…), (24), p.16: `E_{ν_U} Q^c_0 ≤ σn/2` for the invariant
law `ν_U` of the cover rule, on a source of size `n ≥ n₀`. -/
theorem lemma_4_10 (H : GraphInput) (K : ℕ) (hH : IsSourceRange H K)
    (U : Finset (Fin H.N)) (o : Fin (edgeCount H) → Fin H.N) (hU : U.card = K)
    (ho : IsCoverAssignment H U o) (ν : State (H.N + (edgeCount H + 1)) → ℝ)
    (hν : IsInvariantLaw (ffInstance H K) (coverRule U o) ν) (hn : n0FF ≤ H.N) :
    nuMean ν (fun q => (q flexIdx : ℝ≥0∞)) ≤
      ENNReal.ofReal ((sigmaFF : ℝ) * (H.N : ℝ) / 2) := by sorry

end ImpatientMatching
