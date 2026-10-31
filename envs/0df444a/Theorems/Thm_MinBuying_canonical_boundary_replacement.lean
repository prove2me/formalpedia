-- Prove2me | Theorems.Thm_MinBuying_canonical_boundary_replacement
-- name    : MinBuying.canonical_boundary_replacement
-- status  : Proved
-- author  : @mikeh
-- created : 2026-10-30T17:38:37.962239+00:00
-- url     : https://prove2.me/theorems/cd04d19e-cd3f-4cec-a353-36ce38eb8031
-- title:
--   Canonical boundary replacement at the first continuation crossing
-- statement:
--   Let a>0, p>1 and 0≤C≤1. Write D=(a+C)/(1+a/p), and suppose D>1 and p[1−p²/((p+C)(p+a))]≤1. Set b=p(D−1)/(p−D). Then b>0, D<p, D≤1+C, and the new continuation from one is exactly D. Moreover,
--
--   $$(t+1)(t+b)\le(t+C)(t+a)\qquad(t\ge0).$$
--
--   For every ε≥0 and z≥1−ε, the new continuation (b+z)/(1+b/p) is at least D−ε. These identities and inequalities justify the boundary-item replacement in the canonical reduction: it preserves the desired continuation, respects every uniform-price constraint, and controls the loss from a finite terminal cap.
-- source:
--   Cui, Hamilton, Lamperski, and Ganjizadeh Tari, Unit-Demand Pricing for Min-Buying Customers, September 27, 2026 manuscript, https://doi.org/10.2139/ssrn.5178133, proof of Lemma 2, ec9–ec11, equations EC.13–EC.16.

import Definitions.Def_MinBuying_Triangular

namespace MinBuying

/-- Scalar boundary replacement in the proof of Lemma 2, equations
EC.13--EC.16. The previous continuation is at most one and the new one
exceeds one; the uniform-price constraint makes the replacement feasible. -/
theorem canonical_boundary_replacement (a p C : ℝ)
    (ha : 0 < a) (hp : 1 < p) (hC0 : 0 ≤ C) (hC1 : C ≤ 1)
    (hcross : 1 < continuationStep a p C)
    (hUP : p * (1 - (p / (p + C)) * (p / (p + a))) ≤ 1) :
    let D := continuationStep a p C
    let b := p * (D - 1) / (p - D)
    0 < b ∧ D < p ∧ D ≤ 1 + C ∧ continuationStep b p 1 = D ∧
      (∀ t : ℝ, 0 ≤ t → (t + 1) * (t + b) ≤ (t + C) * (t + a)) ∧
      (∀ ε z : ℝ, 0 ≤ ε → 1 - ε ≤ z → D - ε ≤ continuationStep b p z) := by
  sorry

end MinBuying
