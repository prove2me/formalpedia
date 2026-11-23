-- Prove2me | Theorems.Thm_MarketInterference_FluidBias_Supplement_theorem_11_counterexample
-- name    : MarketInterference.FluidBias.Supplement.theorem_11_counterexample
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-23T20:49:33.466669+00:00
-- url     : https://prove2.me/theorems/26665845-cdb6-4768-9bb3-2fa39cec7828
-- title:
--   Theorem 11 (companion theorem; not used in the proof of the goal) (corrected: zero-effect refutation)
-- statement:
--   The strict nonzero RCT-bias conclusion (26) of Theorem 11 is false on an allowed instance. Take one demand type, one supply type, value 1 and no arc capacity. Set the fixed profiles α=γ=1, request probability p=1 and treatment increment q=0, so that at index n the intent and demand scale is λ̄_n=λ_n=n+2, supply scale π̄_n=π_n=1 and β_n=0. Fix ρ=1/2. All rates are nonnegative, β≥0 and λ̄_n/π̄_n→∞. The one-variable matching program has unique primal x=1 and unique dual (a,b)=(0,1), at every partial-treatment state. Its value is
--   $$
--   \Phi^b(d,s)=\sup\{x\in\mathbb R:0\le x,\ x\le d,\ x\le s\}.
--   $$
--   At these positive rates this is an attained finite maximum. The true effect Δ_n, fluid RCT estimate (1/λ_n)β_n and SP estimate 0·β_n all equal zero. Consequently both undersupply biases tend to zero; the RCT bias has no nonzero real limit. This refutes the complete printed theorem's strict clause. It does not replace it with a restricted positive theorem or omit an unrefuted required clause silently.
--
--   **Formalization Note** The scalar program inside the statement is exactly uncapacitated (1) with value 1, not the finite-capacity network used for the other companions. The uniqueness predicates optimize the actual primal and dual objectives. The fixed profiles have ℓ1 norm 1 and q=0 is permitted by q∈[−p,1−p]. Assumption 1 is immaterial to the fluid formulas and is realizable by uniform allocation among indistinguishable units. The positive demand n+2 ensures the displayed division never uses zero.
--
--   Differences from the source:
--   - correction: the full Theorem 11, including a strict nonzero undersupply RCT-bias limit → an explicit source-admissible counterexample with zero RCT and SP bias; reason: β=0 is permitted, and both fluid estimators and the true effect then vanish; no generally valid strict conclusion can retain the printed domain
--   - encoding: the uncapacitated bipartite program → its one-demand one-supply value-1 scalar specialization, with explicit primal/dual uniqueness and ratio limit; reason: one admitted instance suffices to refute the universal theorem; this is a refutation, not a narrowed positive replacement
-- source:
--   Bright, Delarue and Lobel, Reducing Marketplace Interference Bias Via Shadow Prices, arXiv:2205.02274v4, p. 37, Theorem 11, (25)–(26); pp. 36–37, Appendix B; pp. 49–50, proof

import Mathlib

namespace MarketInterference.FluidBias.Supplement

open Filter

/-- The allowed zero treatment effect refutes the strict nonzero RCT-bias limit in (26).
The scalar LP is exactly (1) for one demand type, one supply type and value 1, with no arc cap. -/
theorem theorem_11_counterexample :
    let lam : ℕ → ℝ := fun n => (n : ℝ) + 2
    let pi : ℕ → ℝ := fun _ => 1
    let beta : ℕ → ℝ := fun _ => 0
    let value : ℝ → ℝ → ℝ := fun d s => sSup {x : ℝ | 0 ≤ x ∧ x ≤ d ∧ x ≤ s}
    let delta : ℕ → ℝ := fun n => value (lam n + beta n) (pi n) - value (lam n) (pi n)
    let rct : ℕ → ℝ := fun n => (1 / (lam n + (1/2) * beta n)) * beta n
    let sp : ℕ → ℝ := fun n => 0 * beta n
    (∀ n, 0 < lam n ∧ 0 < pi n ∧ 0 ≤ beta n ∧
      (∃! x : ℝ, (0 ≤ x ∧ x ≤ lam n ∧ x ≤ pi n) ∧
        ∀ y : ℝ, 0 ≤ y → y ≤ lam n → y ≤ pi n → y ≤ x) ∧
      (∃! ab : ℝ × ℝ, (0 ≤ ab.1 ∧ 0 ≤ ab.2 ∧ 1 ≤ ab.1 + ab.2) ∧
        ∀ cd : ℝ × ℝ, 0 ≤ cd.1 → 0 ≤ cd.2 → 1 ≤ cd.1 + cd.2 →
          ab.1 * lam n + ab.2 * pi n ≤ cd.1 * lam n + cd.2 * pi n) ∧
      value (lam n) (pi n) = 1 ∧ delta n = 0 ∧ rct n = 0 ∧ sp n = 0) ∧
    Tendsto (fun n => lam n / pi n) atTop atTop ∧
    Tendsto (fun n => |sp n - delta n|) atTop (nhds 0) ∧
    Tendsto (fun n => |rct n - delta n|) atTop (nhds 0) ∧
    ¬ ∃ b : ℝ, b ≠ 0 ∧ Tendsto (fun n => |rct n - delta n|) atTop (nhds b) := by sorry

end MarketInterference.FluidBias.Supplement
