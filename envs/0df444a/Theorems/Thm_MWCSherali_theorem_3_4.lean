-- Prove2me | Theorems.Thm_MWCSherali_theorem_3_4
-- name    : MWCSherali.theorem_3_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T12:13:50.275257+00:00
-- url     : https://prove2.me/theorems/461c7e38-caad-4b1b-83b3-86407a5ed5e1
-- title:
--   Theorem 3.4 — the continuous Flow LP is the limit of the discrete one
-- statement:
--   For every $k\ge2$ and $n\ge1$,
--
--   $$\frac{q_{k,n}}{n+1}\ \le\ Q_k\ \le\ \frac{q_{k,n}}{n},$$
--
--   and consequently, for every $k\ge2$,
--
--   $$\lim_{n\to\infty}\frac{q_{k,n}}n=Q_k .$$
--
--   So an explicit feasible solution of the continuous LP bounds $q_{k,n}/n$ for every $n$, and hence (Theorem 3.2, Lemma 2.5) gives UG-hardness of Multiway Cut.
--
--   Differences from the source:
--   - encoding: points x ∈ Δ_{k,n} with coordinates in (1/n)ℤ, 1-based indices → integer coordinates y = n x (Grid k n), 0-based indices; reason: Lean convention; the same points
--   - encoding: φ ∈ C^{(1)}(Δ_k), continuously differentiable on Δ_k → ContDiff ℝ 1 φ on all of ℝ^k; reason: the constraints use only values on Δ_k and derivatives tangent to Δ_k, and every C¹ function on Δ_k agrees there with a global C¹ function
--   - encoding: Borel measures on Δ_k, probability measures on Γ_a → measures on Fin k → ℝ giving the complement of Δ_k (resp. Γ_a) measure 0; reason: Lean convention; the same measures
--   - encoding: nonnegative capacity measures B_i → B_i required to be finite measures; reason: an infinite capacity has objective ∞ and changes no infimum; it makes every integral a genuine one
--   - encoding: q_{k,n} and Q_k as minimum/infimum of real objectives → infima in [0, ∞] (ℝ≥0∞), quotients as ℝ≥0∞ divisions; reason: the objectives are nonnegative; an ℝ≥0∞ infimum has no junk value on an empty set
-- source:
--   Brakensiek–Huang–Potechin–Zwick, Improved lower bounds on the approximability of Multiway Cut using Sherali–Adams relaxations, arXiv:2611.05511 (version of Nov. 3, 2026), Theorem 3.4, p.28

import Mathlib
import Definitions.Def_MWCSherali_qFlow
import Definitions.Def_MWCSherali_Qcont

namespace MWCSherali

open Filter Topology
open scoped ENNReal

/-- **Theorem 3.4 (the continuous Flow LP is the limit of the discrete one).** Brakensiek–Huang–Potechin–Zwick, arXiv:2611.05511 (version of Nov. 3, 2026),
Theorem 3.4, p.28: "For every `k ≥ 2` and `n ≥ 1`, we have `q_{k,n}/(n + 1) ≤ Q_k ≤ q_{k,n}/n`.
Consequently, for every `k ≥ 2` we have `lim_{n→∞} q_{k,n}/n = Q_k`."

**Formalization Note.** `q_{k,n}` (`qFlow`) and `Q_k` (`Qcont`) are infima in `ℝ≥0∞`, and the
quotients are `ℝ≥0∞` divisions by the positive naturals `n + 1` and `n`. -/
theorem theorem_3_4 (k : ℕ) (hk : 2 ≤ k) :
    (∀ n : ℕ, 1 ≤ n → qFlow k n / ((n : ℝ≥0∞) + 1) ≤ Qcont k ∧ Qcont k ≤ qFlow k n / n) ∧
      Tendsto (fun n : ℕ => qFlow k n / n) atTop (𝓝 (Qcont k)) := by sorry

end MWCSherali
