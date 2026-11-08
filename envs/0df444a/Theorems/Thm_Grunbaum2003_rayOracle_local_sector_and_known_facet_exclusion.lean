-- Prove2me | Theorems.Thm_Grunbaum2003_rayOracle_local_sector_and_known_facet_exclusion
-- name    : Grunbaum2003.rayOracle_local_sector_and_known_facet_exclusion
-- status  : Proved
-- author  : @kmehltretter82
-- created : 2026-11-07T18:41:17.413201+00:00
-- url     : https://prove2.me/theorems/8a258753-f6c3-45f7-ba23-abab729b9f8f
-- title:
--   Outer-vertex probe slackness and explicit field-arithmetic local sector exclusion of known facets
-- statement:
--   This theorem establishes the outer-approximation vertex probe criteria and the explicit field-arithmetic local sector exclusion of already discovered facets in the Gritzmann–Klee–Westwater ray-oracle reconstruction algorithm:
--
--   1. **Outer-approximation vertex probe (`rayOracle_outer_vertex_fixed_iff`, `outer_vertex_probe_known_facets_strict`, `rayOracle_known_nonpositive_direction_strict`):** For any closed convex body $P \subseteq Q \subseteq \mathbb{R}^d$ ($d \ge 1$) with $0 \in \operatorname{int}(P)$ and any extreme point $x \in \operatorname{ext}(Q)$, $x \neq 0$ and $\operatorname{oracle}(x) = x \iff x \in \operatorname{ext}(P)$. When $\operatorname{oracle}(x) \neq x$ and $L_j(x) \le 1$ for a finite family of known facet functionals $L_j$, the boundary point $p = \operatorname{oracle}(x)$ satisfies $L_j(p) < 1$ for all $j$ (and similarly for any ray $x \neq 0$ with $L_j(x) \le 0$).
--   2. **Field-arithmetic slack and direction bounds (`known_facet_field_parameters`):** Given $L_j(p) < 1$ for $j \in \operatorname{Fin} k$, the rational-expression slack $\delta = \prod_j \frac{1 - L_j(p)}{1 + (1 - L_j(p))} > 0$ and sum-of-squares bound $M = 1 + \sum_j L_j(u)^2 \ge 0$ satisfy $L_j(p) \le 1 - \delta$ and $|L_j(u)| \le M$ for all $j$ without min/max branching or square roots.
--   3. **Uniform local sector and first-reference segment exclusion (`scaled_planar_first_two_queries_avoid_known_facets`, `first_reference_segment_avoids_known_facets`):** With step size $\varepsilon = \frac{a \delta}{2(1 + a M + \delta)}$ (where $\pm a u \in P$), the initial perturbed direction $p - \varepsilon u$, the second direction $r_2 = \frac{\tau}{1+\tau} \varepsilon u + \frac{2}{1+\tau} p$, and every point $p + x(r_2 - p)$ ($0 \le x \le 1$) along the first reference segment are nonzero and have oracle replies strictly inside every known halfspace $L_j < 1$.
-- source:
--   Grünbaum 2003, Convex Polytopes (2nd ed., Graduate Texts in Mathematics 221), §3.6, pp. 52b–52c (citing Gritzmann–Klee–Westwater 1995)

import Definitions.Def_Grunbaum2003_IsPolytopeRayOracle
import Definitions.Def_Grunbaum2003_IsDPolytope
import Mathlib.Analysis.Convex.Slope
import Mathlib.Analysis.Convex.Topology
import Mathlib.Analysis.Convex.Strict.Extreme
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

set_option autoImplicit false
open scoped BigOperators

namespace Grunbaum2003

theorem rayOracle_local_sector_and_known_facet_exclusion :
    (∀ {d : ℕ} (hd : 0 < d) {P Q : Set (Fin d → ℝ)},
      Convex ℝ P → IsClosed P → (0 : Fin d → ℝ) ∈ interior P → P ⊆ Q →
      ∀ {oracle : (Fin d → ℝ) → (Fin d → ℝ)}, IsPolytopeRayOracle P oracle →
      ∀ {x : Fin d → ℝ}, x ∈ Q.extremePoints ℝ →
        x ≠ 0 ∧ (oracle x = x ↔ x ∈ P.extremePoints ℝ)) ∧
    (∀ {d k : ℕ} (hd : 0 < d) {P Q : Set (Fin d → ℝ)},
      Convex ℝ P → IsClosed P → (0 : Fin d → ℝ) ∈ interior P → P ⊆ Q →
      ∀ {oracle : (Fin d → ℝ) → (Fin d → ℝ)}, IsPolytopeRayOracle P oracle →
      ∀ {x : Fin d → ℝ}, x ∈ Q.extremePoints ℝ → oracle x ≠ x →
      ∀ (L : Fin k → (Fin d → ℝ) →ₗ[ℝ] ℝ), (∀ j, L j x ≤ 1) →
        x ≠ 0 ∧ (∀ j, L j (oracle x) < 1)) ∧
    (∀ {d k : ℕ} {P : Set (Fin d → ℝ)} {oracle : (Fin d → ℝ) → (Fin d → ℝ)},
      IsPolytopeRayOracle P oracle →
      ∀ (L : Fin k → (Fin d → ℝ) →ₗ[ℝ] ℝ) {x : Fin d → ℝ},
        x ≠ 0 → (∀ j, L j x ≤ 0) → ∀ j, L j (oracle x) < 1) ∧
    (∀ {d k : ℕ} (L : Fin k → (Fin d → ℝ) →ₗ[ℝ] ℝ) (p u : Fin d → ℝ),
      (∀ j, L j p < 1) →
      let δ := ∏ j, (1 - L j p) / (1 + (1 - L j p))
      let M := 1 + ∑ j, (L j u) ^ 2
      0 < δ ∧ 0 ≤ M ∧ (∀ j, L j p ≤ 1 - δ) ∧ (∀ j, |L j u| ≤ M)) ∧
    (∀ {d : ℕ} {ι : Type*} {P : Set (Fin d → ℝ)},
      Convex ℝ P → IsClosed P → (0 : Fin d → ℝ) ∈ interior P →
      ∀ {p u : Fin d → ℝ}, p ∈ frontier P →
      ∀ {a δ M : ℝ}, 0 < a → 0 < δ → 0 ≤ M →
      (-a) • u ∈ P → a • u ∈ P →
      ∀ (L : ι → (Fin d → ℝ) →ₗ[ℝ] ℝ),
      (∀ j, L j p ≤ 1 - δ) → (∀ j, |L j u| ≤ M) →
      ∀ {oracle : (Fin d → ℝ) → (Fin d → ℝ)}, IsPolytopeRayOracle P oracle →
      let ε := a * δ / (2 * (1 + a * M + δ))
      (p - ε • u ≠ 0 ∧
        ∃ τ : ℝ, 0 < τ ∧ τ < 2 ∧
          oracle (p - ε • u) = τ • (p - ε • u) ∧
          (∀ j, L j (oracle (p - ε • u)) < 1) ∧
          let r₂ := (τ / (1 + τ)) • (ε • u) + (2 / (1 + τ)) • p
          r₂ ≠ 0 ∧ (∀ j, L j (oracle r₂) < 1) ∧
          ∀ x : ℝ, 0 ≤ x → x ≤ 1 →
            p + x • (r₂ - p) ≠ 0 ∧ ∀ j, L j (oracle (p + x • (r₂ - p))) < 1)) := by sorry

end Grunbaum2003
