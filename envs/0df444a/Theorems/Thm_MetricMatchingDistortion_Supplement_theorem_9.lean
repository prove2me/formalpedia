-- Prove2me | Theorems.Thm_MetricMatchingDistortion_Supplement_theorem_9
-- name    : MetricMatchingDistortion.Supplement.theorem_9
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T02:05:49.841207+00:00
-- url     : https://prove2.me/theorems/9037c9f1-0ea7-4f9a-ad28-25436b151783
-- title:
--   Theorem 9 — PS has distortion $O((10/9)^{n/2})$
-- statement:
--   There is a constant $C$ such that for every $n\ge1$, every instance $\sigma$ with $n$ agents, every pseudometric $d$ consistent with $\sigma$ and every perfect matching $\pi^*$,
--   $$\mathbb E_{M\sim\mathrm{PS}(\sigma)}[\mathrm{cost}(M,d)]=\mathrm{cost}(X(1),d)\ \le\ C\,(10/9)^{n/2}\,\mathrm{cost}(\pi^*,d).$$
--   Hence $\mathrm{distortion}(\mathrm{PS},\sigma)=O((10/9)^{n/2})$ for every instance.
--
--   Together with Theorem 8 this determines the distortion of PS up to a constant factor.
--
--   Differences from the source:
--   - encoding: O(f(n)) → ∃ C chosen before n, the instance, the metric (and Y), with E[cost] ≤ C · f(n) · cost(π*, d); reason: the page states the constant is independent of n, σ and d; same convention as HasDistortionO
--   - encoding: distortion(M, σ) ≤ B (supremum of E[cost]/min cost, footnote 10) → E[cost] ≤ B · cost(π*, d) for every consistent d and every perfect matching π*; reason: for OPT > 0 take π* optimal; for OPT = 0 the page's c/0 = +∞ forces E[cost] = 0 and 0/0 = 1 ≤ B; same convention as the published HasDistortionO
--   - encoding: E_{M∼PS(σ)}[cost(M, d)] → fracCost (psAlloc rk 1) d = cost(X(1), d); reason: the page's own identity E_{M∼PS(σ)}[cost(M, d)] = cost(X(1), d) (p.46); X is the published PS trajectory psAlloc
--   - encoding: n ≥ 1 (standing assumption, §2 p.9) → [NeZero n] (required by the published psAlloc); reason: the same condition as a type class
-- source:
--   Charikar, Haqi, Hastings, Huang, Ramakrishnan, Sublinear Metric Distortion for Matching, arXiv:2611.05777 (held version, sha256 fdf3452b105082d6ff680c8a762ec950298417efdebeb216b721705a9802e0da), Theorem 9, p.51 (PDF p.53); constant independent of n, σ, d, p.62 (PDF p.64)

import Mathlib
import Definitions.Def_MetricMatchingDistortion_IsConsistentPseudometric
import Definitions.Def_MetricMatchingDistortion_matchingCost
import Definitions.Def_MetricMatchingDistortion_IsPartialFractionalMatching
import Definitions.Def_MetricMatchingDistortion_psAlloc

namespace MetricMatchingDistortion.Supplement

open MetricMatchingDistortion

/-- **Theorem 9 (PS upper bound).** Charikar et al., *Sublinear Metric Distortion for Matching*,
arXiv:2611.05777 (held version, sha256 fdf3452b…), Theorem 9, p.51 (PDF p.53): "For every instance
σ, distortion(PS, σ) = O((10/9)^{n/2})."

There is one constant `C` such that for every `n ≥ 1`, every ranking profile `rk`, every consistent
pseudometric `d` and every perfect matching `π*`,
`E_{M∼PS(rk)}[cost(M, d)] = cost(X(1), d) ≤ C · (10/9)^{n/2} · cost(π*, d)`.

**Formalization Note.** `O(·)` is one `C` chosen before `n`, the instance and the metric (p.62:
"the constant … is independent of n, σ, and d"), as in the base mission's `HasDistortionO`; the
ratio is written as an inequality against every perfect matching (an optimum of `0` forces cost
`0`, the page's `c/0 = +∞`). The expected cost of PS is `cost(X(1), d)` (p.46), with `X` the base
mission's `psAlloc`. -/
theorem theorem_9 :
    ∃ C : ℝ, ∀ (n : ℕ) [NeZero n] (rk : Ranking n) (d : Fin n ⊕ Fin n → Fin n ⊕ Fin n → ℝ),
      IsConsistentPseudometric rk d → ∀ πstar : Equiv.Perm (Fin n),
        fracCost (psAlloc rk 1) d ≤ C * (10 / 9 : ℝ) ^ ((n : ℝ) / 2) * matchingCost πstar d := by sorry

end MetricMatchingDistortion.Supplement
