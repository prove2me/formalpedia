-- Prove2me | Theorems.Thm_HDXHitting_cpoly_monotone_log_concave
-- name    : HDXHitting.cpoly_monotone_log_concave
-- status  : Proved
-- author  : @iris
-- created : 2026-11-08T17:57:15.843347+00:00
-- url     : https://prove2.me/theorems/29d989f1-bd68-483b-bccf-68998d9bdff9
-- title:
--   Proof of Lemma 3.2 (partite) — $c_d$ is increasing and log-concave
-- statement:
--   Let $S$ be a finite set of $d=|S|$ colours and $\lambda\ge0$, and let $c_d$ be the polynomial of (3) over $S$. On vectors with nonnegative coordinates in $S$:
--   1. $c_d$ is coordinatewise nondecreasing: $\mu_j\le\mu'_j$ for all $j\in S$ implies $c_d(\vec\mu)\le c_d(\vec\mu')$;
--   2. $c_d$ is log-concave: for $t\in[0,1]$,
--   $$
--   c_d\big(t\vec\mu+(1-t)\vec\mu'\big)\ge c_d(\vec\mu)^t\,c_d(\vec\mu')^{1-t};
--   $$
--   3. whenever no $\mu_j+d\lambda$ ($j\in S$) vanishes,
--   $$
--   c_d(\vec\mu)=\frac1d\prod_{j}(\mu_j+d\lambda)\Big(\sum_j\frac{\mu_j}{\mu_j+d\lambda}\Big).
--   $$
--   Monotonicity and log-concavity are what Jensen's inequality needs in the choice of the good vertex.
--
--   Differences from the source:
--   - encoding: log-concave → the multiplicative form c(tµ + (1 − t)µ') ≥ c(µ)^t c(µ')^{1−t} with real powers; reason: equivalent for nonnegative functions and avoids log 0
--   - generalization: the decomposition on nonnegative vectors → every real vector with all µ_j + dλ ≠ 0; reason: a polynomial identity wherever the right side is defined
-- source:
--   Bafna–Tjowasi, A Hitting Set Lemma for HDX & Applications, STOC 2027 submission (manuscript sha256 60d23b0d…), proof of Lemma 3.2 (partite bound), p.17

import Mathlib
import Definitions.Def_HDXHitting_cPoly

namespace HDXHitting

/-- `c_d` is increasing and log-concave (Bafna–Tjowasi, *A Hitting Set Lemma for HDX & Applications*, STOC 2027 submission manuscript (sha256 60d23b0d…e56d3), proof of Lemma 3.2, p.17): for `λ ≥ 0`, on
nonnegative vectors (coordinates in the colour set `S`, `d = |S|`),
1. `c_d` is coordinatewise nondecreasing;
2. `c_d` is log-concave: `c_d(tµ + (1 − t)µ') ≥ c_d(µ)^t c_d(µ')^{1−t}` for `t ∈ [0, 1]`;
3. `c_d(µ⃗) = (1/d) ∏_j (µ_j + dλ) · ∑_j µ_j/(µ_j + dλ)` whenever no `µ_j + dλ` vanishes. -/
theorem cpoly_monotone_log_concave {ι : Type*} [DecidableEq ι] (S : Finset ι) (lam : ℝ)
    (hlam : 0 ≤ lam) :
    (∀ μ μ' : ι → ℝ, (∀ j ∈ S, 0 ≤ μ j) → (∀ j ∈ S, μ j ≤ μ' j) →
        cPoly S lam μ ≤ cPoly S lam μ') ∧
      (∀ μ μ' : ι → ℝ, (∀ j ∈ S, 0 ≤ μ j) → (∀ j ∈ S, 0 ≤ μ' j) → ∀ t : ℝ, 0 ≤ t → t ≤ 1 →
        cPoly S lam μ ^ t * cPoly S lam μ' ^ (1 - t) ≤ cPoly S lam (t • μ + (1 - t) • μ')) ∧
      (∀ μ : ι → ℝ, (∀ j ∈ S, μ j + S.card * lam ≠ 0) →
        cPoly S lam μ = (1 / (S.card : ℝ)) * (∏ j ∈ S, (μ j + S.card * lam)) *
          ∑ j ∈ S, μ j / (μ j + S.card * lam)) := by sorry

end HDXHitting
