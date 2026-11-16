-- Prove2me | Theorems.Thm_MetricMatchingDistortion_Supplement_theorem_7
-- name    : MetricMatchingDistortion.Supplement.theorem_7
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T02:08:24.954331+00:00
-- url     : https://prove2.me/theorems/cab6b70d-7d8a-4ae9-9666-a68d228bb629
-- title:
--   Theorem 7 — deterministic truthful Pareto-optimal mechanisms have distortion at least $2^n-1$
-- statement:
--   Let $M$ be a deterministic matching mechanism that is truthful (no agent obtains a strictly preferred item by misreporting) and Pareto optimal (every output is a Pareto optimal perfect matching). Then for every $n\ge1$ there exist an instance $\sigma$ with $n$ agents and a pseudometric $d$ consistent with $\sigma$ with $\mathrm{OPT}>0$ and
--   $$\mathrm{cost}(M(\sigma),d)\ \ge\ (2^n-1)\,\mathrm{OPT}.$$
--   Hence $M$ has distortion at least $2^n-1$.
--
--   The bound equals the cost ratio $2^n-1$ of left-to-right serial dictatorship on the line instance of Figure 1.
--
--   Differences from the source:
--   - reading: distortion(M, σ) ≥ L, with distortion the supremum over d ∈ ρ(σ) of E[cost]/min cost (footnote 10: 0/0 = 1, c/0 = +∞) → one pseudometric d consistent with σ with 0 < OPT = min_π cost(π, d) and E[cost] ≥ L · OPT; reason: such a d bounds the supremum from below; requiring OPT > 0 excludes the vacuous case OPT = 0, and every lower-bound instance of the paper has a positive optimum
--   - encoding: deterministic mechanism; truthful; Pareto optimal → DetMechanism (rankings ↦ one perfect matching); IsDetTruthful (rk a does not strictly prefer M(rk')(a) to M(rk)(a) when rk' differs from rk only at a); IsParetoOptimalDet (every output Pareto optimal, p.11); reason: the definitions of p.10–11
--   - encoding: n agents (any instance size) → every n ≥ 1; reason: the standing assumption n ≥ 1 of §2; the instance may depend on M
-- source:
--   Charikar, Haqi, Hastings, Huang, Ramakrishnan, Sublinear Metric Distortion for Matching, arXiv:2611.05777 (held version, sha256 fdf3452b105082d6ff680c8a762ec950298417efdebeb216b721705a9802e0da), Theorem 7, p.67 (PDF p.69)

import Mathlib
import Definitions.Def_MetricMatchingDistortion_IsConsistentPseudometric
import Definitions.Def_MetricMatchingDistortion_matchingCost
import Definitions.Def_MetricMatchingDistortion_Supplement_optCost
import Definitions.Def_MetricMatchingDistortion_Supplement_Truthful

namespace MetricMatchingDistortion.Supplement

open MetricMatchingDistortion

/-- **Theorem 7 (deterministic truthful Pareto-optimal mechanisms).** Charikar et al., *Sublinear
Metric Distortion for Matching*, arXiv:2611.05777 (held version, sha256 fdf3452b…), Theorem 7, p.67
(PDF p.69): "Every deterministic truthful mechanism that is Pareto optimal has distortion at least
2^n − 1."

For every deterministic mechanism `M` that is truthful and Pareto optimal on every instance, and
every `n ≥ 1`, there are a ranking profile `rk` on `n` agents and items and a consistent
pseudometric `d` with positive optimum `OPT` and `cost(M(rk), d) ≥ (2^n − 1) · OPT`.

**Formalization Note.** The bound is exact (no `Ω`) and holds for every `n ≥ 1`. The instance may
depend on `M` (the proof relabels the agents). A lower bound on the distortion is witnessed by one
consistent `d` with `OPT > 0` (the proof's line instance has `OPT = 1`). Truthfulness is the
ordinal one of p.10: no agent obtains an item she strictly prefers by misreporting. -/
theorem theorem_7 (M : DetMechanism) (hT : IsDetTruthful M) (hP : IsParetoOptimalDet M)
    (n : ℕ) (hn : 1 ≤ n) :
    ∃ rk : Ranking n, ∃ d : Fin n ⊕ Fin n → Fin n ⊕ Fin n → ℝ, IsConsistentPseudometric rk d ∧
      0 < optCost d ∧ ((2 : ℝ) ^ n - 1) * optCost d ≤ matchingCost (M n rk) d := by sorry

end MetricMatchingDistortion.Supplement
