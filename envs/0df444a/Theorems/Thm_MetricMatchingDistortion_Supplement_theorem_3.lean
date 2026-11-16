-- Prove2me | Theorems.Thm_MetricMatchingDistortion_Supplement_theorem_3
-- name    : MetricMatchingDistortion.Supplement.theorem_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T02:06:35.707392+00:00
-- url     : https://prove2.me/theorems/21b21563-ec00-43e1-af43-0602fd4be4f2
-- title:
--   Theorem 3 — TruncatedPS with doubling has distortion $O(n)$
-- statement:
--   There is a constant $C$ such that for every $n\ge1$, every instance $\sigma$ with $n$ agents, every pseudometric $d$ consistent with $\sigma$, every output $Y$ that Algorithm 8 may return (a bistochastic matrix with $Y\le 2X(1-\frac1{2n})$ entrywise) and every perfect matching $\pi^*$,
--   $$\mathbb E_{M\sim\mathrm{TruncPS}(\sigma)}[\mathrm{cost}(M,d)]=\mathrm{cost}(Y,d)\ \le\ C\,n\,\mathrm{cost}(\pi^*,d).$$
--   Hence Algorithm 8 has distortion $O(n)$ on every instance.
--
--   Stopping PS slightly before time $1$ and doubling the prefix removes the exponential blow-up of Theorem 8.
--
--   Differences from the source:
--   - encoding: O(f(n)) → ∃ C chosen before n, the instance, the metric (and Y), with E[cost] ≤ C · f(n) · cost(π*, d); reason: the page states the constant is independent of n, σ and d; same convention as HasDistortionO
--   - encoding: distortion(M, σ) ≤ B (supremum of E[cost]/min cost, footnote 10) → E[cost] ≤ B · cost(π*, d) for every consistent d and every perfect matching π*; reason: for OPT > 0 take π* optimal; for OPT = 0 the page's c/0 = +∞ forces E[cost] = 0 and 0/0 = 1 ≤ B; same convention as the published HasDistortionO
--   - encoding: E_{M∼TruncPS(σ)}[cost(M, d)] with Y read as a lottery with marginals Y → fracCost Y d for every Y with IsTruncPSOutput rk Y (bistochastic, Y ≤ 2·X(1 − 1/(2n)) entrywise); reason: Algorithm 8 may return any such Y and the cost of a lottery with marginals Y is cost(Y, d); the bound is stated for every admissible Y
--   - encoding: n ≥ 1 (standing assumption, §2 p.9) → [NeZero n] (required by the published psAlloc); reason: the same condition as a type class
-- source:
--   Charikar, Haqi, Hastings, Huang, Ramakrishnan, Sublinear Metric Distortion for Matching, arXiv:2611.05777 (held version, sha256 fdf3452b105082d6ff680c8a762ec950298417efdebeb216b721705a9802e0da), Theorem 3, p.63 (PDF p.65)

import Mathlib
import Definitions.Def_MetricMatchingDistortion_IsConsistentPseudometric
import Definitions.Def_MetricMatchingDistortion_matchingCost
import Definitions.Def_MetricMatchingDistortion_IsPartialFractionalMatching
import Definitions.Def_MetricMatchingDistortion_Supplement_IsTruncPSOutput

namespace MetricMatchingDistortion.Supplement

open MetricMatchingDistortion

/-- **Theorem 3 (TruncatedPS with doubling).** Charikar et al., *Sublinear Metric Distortion for
Matching*, arXiv:2611.05777 (held version, sha256 fdf3452b…), Theorem 3, p.63 (PDF p.65): "For
every instance σ, Algorithm 8 has distortion O(n)."

There is one constant `C` such that for every `n ≥ 1`, every ranking profile `rk`, every consistent
pseudometric `d`, every output `Y` Algorithm 8 may return (bistochastic, `Y ≤ 2X(1 − 1/(2n))`
entrywise) and every perfect matching `π*`,
`E_{M∼TruncPS(rk)}[cost(M, d)] = cost(Y, d) ≤ C · n · cost(π*, d)`.

**Formalization Note.** `O(n)` is one `C` chosen before `n`, the instance, the metric and `Y`; the
ratio is written as an inequality against every perfect matching, as in the base mission's
`HasDistortionO`. The bound holds for every admissible `Y`, since Algorithm 8 may return any. -/
theorem theorem_3 :
    ∃ C : ℝ, ∀ (n : ℕ) [NeZero n] (rk : Ranking n) (d : Fin n ⊕ Fin n → Fin n ⊕ Fin n → ℝ),
      IsConsistentPseudometric rk d → ∀ Y : Fin n → Fin n → ℝ, IsTruncPSOutput rk Y →
        ∀ πstar : Equiv.Perm (Fin n), fracCost Y d ≤ C * (n : ℝ) * matchingCost πstar d := by sorry

end MetricMatchingDistortion.Supplement
