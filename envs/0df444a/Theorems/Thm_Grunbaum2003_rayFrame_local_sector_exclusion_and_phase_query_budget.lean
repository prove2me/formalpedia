-- Prove2me | Theorems.Thm_Grunbaum2003_rayFrame_local_sector_exclusion_and_phase_query_budget
-- name    : Grunbaum2003.rayFrame_local_sector_exclusion_and_phase_query_budget
-- status  : Proved
-- author  : @kmehltretter82
-- created : 2026-11-09T02:51:03.731399+00:00
-- url     : https://prove2.me/theorems/635e6f0e-bd88-4ec8-bd30-85300dd8c381
-- title:
--   Local Sector Known-Facet Exclusion over Finset S and Facet-Discovery Phase Query Budget
-- statement:
--   Proves the single-step extension query bound q + 1 + 1 + 1 + n <= q + (2 * (m - cardS) + 3) when 3 + n <= 2 * (m - cardS) + 2, the inductive (d - 1)-step facet-discovery phase query bound q_step (d - 1) <= q_start + (1 + (d - 1) * (2 * (m - cardS) + 3)), and the local sector known-facet exclusion L j (oracle (p + x • (r2 - p))) < 1 for all j in S and x in [0, 1].
-- source:
--   Gritzmann, Klee, Westwater (1995), §5.2–5.5; Grünbaum, Convex Polytopes (2003)

import Definitions.Def_Grunbaum2003_IsPolytopeRayOracle
import Definitions.Def_Grunbaum2003_IsDPolytope
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.Convex.Exposed
import Mathlib.Analysis.Convex.Extreme
import Mathlib.Analysis.Convex.Hull
import Mathlib.Order.Interval.Finset.Nat

set_option autoImplicit false
open scoped BigOperators Classical

namespace Grunbaum2003

theorem rayFrame_local_sector_exclusion_and_phase_query_budget (d : ℕ) :
    (∀ (m cardS n q : ℕ),
      3 + n ≤ 2 * (m - cardS) + 2 →
      q + 1 + 1 + 1 + n ≤ q + (2 * (m - cardS) + 3)) ∧
    (∀ (m cardS q_start : ℕ) (q_step : ℕ → ℕ),
      q_step 0 ≤ q_start + 1 →
      (∀ r < d - 1, q_step (r + 1) ≤ q_step r + (2 * (m - cardS) + 3)) →
      q_step (d - 1) ≤ q_start + (1 + (d - 1) * (2 * (m - cardS) + 3))) ∧
    (∀ {m : ℕ} {P : Set (Fin d → ℝ)}, IsDPolytope P → (0 : Fin d → ℝ) ∈ interior P →
      ∀ (L : Fin m → (Fin d → ℝ) →L[ℝ] ℝ), P = {x | ∀ i, L i x ≤ 1} →
      ∀ {oracle : (Fin d → ℝ) → (Fin d → ℝ)}, IsPolytopeRayOracle P oracle →
      ∀ (S : Finset (Fin m)) (eS : Fin S.card ≃ S)
        {p u : Fin d → ℝ}, p ∈ frontier P →
      (∀ j ∈ S, L j p < 1) →
      ∀ {a : ℝ}, 0 < a → (-a) • u ∈ P → a • u ∈ P →
      let LS : Fin S.card → (Fin d → ℝ) →ₗ[ℝ] ℝ := fun j => (L (eS j).val).toLinearMap
      let δ := ∏ j : Fin S.card, (1 - LS j p) / (1 + (1 - LS j p))
      let M := 1 + ∑ j : Fin S.card, (LS j u) ^ 2
      let ε := a * δ / (2 * (1 + a * M + δ))
      p - ε • u ≠ 0 ∧
        ∃ τ : ℝ, 0 < τ ∧ τ < 2 ∧
          oracle (p - ε • u) = τ • (p - ε • u) ∧
          (∀ j ∈ S, L j (oracle (p - ε • u)) < 1) ∧
          let r₂ := (τ / (1 + τ)) • (ε • u) + (2 / (1 + τ)) • p
          r₂ ≠ 0 ∧ (∀ j ∈ S, L j (oracle r₂) < 1) ∧
          ∀ x : ℝ, 0 ≤ x → x ≤ 1 →
            p + x • (r₂ - p) ≠ 0 ∧ ∀ j ∈ S, L j (oracle (p + x • (r₂ - p))) < 1) := by sorry

end Grunbaum2003
