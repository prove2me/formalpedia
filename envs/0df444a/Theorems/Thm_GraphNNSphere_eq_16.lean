-- Prove2me | Theorems.Thm_GraphNNSphere_eq_16
-- name    : GraphNNSphere.eq_16
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T06:38:38.141729+00:00
-- url     : https://prove2.me/theorems/15c6031f-0bf9-4fdb-9f54-7badfc11f4cd
-- title:
--   Eq. (16) — the limits of $I_\vartheta(u\vartheta)$ and $J_\vartheta(u\vartheta)$ as $\vartheta\to0$
-- statement:
--   For each fixed $0<u<\sqrt2$, as $\vartheta\to0^+$,
--   $$I_\vartheta(u\vartheta)\longrightarrow-\frac12\log(1-u^2/4)\quad\text{and}\quad J_\vartheta(u\vartheta)\longrightarrow-\frac12\log\bigl(u^2(1-u^2/4)\bigr),$$
--   and both errors are $O(\vartheta^2)$.
--
--   These limits are what makes the exponent $\gamma_c=\tfrac12\log2$ appear in the dense regime.
--
--   Differences from the source:
--   - encoding: O(ϑ²) → an explicit bound C ϑ² on (0, δ₀), with C, δ₀ depending on u; reason: the standard meaning of the asymptotic notation at this quantifier position (§2.1)
-- source:
--   Lu, Sharp Limits of Graph-Based Nearest Neighbor Search on the Sphere, STOC 2027 submission (manuscript sha256 93565bc5…), proof of Theorem 3.1(b), Eq. (16), p.26

import Mathlib
import Definitions.Def_GraphNNSphere_Jrate
import Definitions.Def_GraphNNSphere_Irate

open Filter Topology

namespace GraphNNSphere

/-- Eq. (16), the limits of the rates as `ϑ → 0` at `ρ = uϑ`, with errors `O(ϑ²)` (Lu, *Sharp Limits
of Graph-Based Nearest Neighbor Search on the Sphere*, STOC 2027 submission (manuscript sha256
93565bc5…), proof of Theorem 3.1(b), Eq. (16), p.26).

**Formalization Note** `O(ϑ²)` is an explicit `C ϑ²` on `(0, δ₀)`, with `C`, `δ₀` depending on `u`. -/
theorem eq_16 (u : ℝ) (hu0 : 0 < u) (hu1 : u < Real.sqrt 2) :
    Tendsto (fun ϑ : ℝ => Irate ϑ (u * ϑ)) (𝓝[>] 0) (𝓝 (-(1 / 2) * Real.log (1 - u ^ 2 / 4))) ∧
    Tendsto (fun ϑ : ℝ => Jrate ϑ (u * ϑ)) (𝓝[>] 0)
      (𝓝 (-(1 / 2) * Real.log (u ^ 2 * (1 - u ^ 2 / 4)))) ∧
    ∃ C δ₀ : ℝ, 0 < δ₀ ∧ ∀ ϑ : ℝ, 0 < ϑ → ϑ < δ₀ →
      |Irate ϑ (u * ϑ) - (-(1 / 2) * Real.log (1 - u ^ 2 / 4))| ≤ C * ϑ ^ 2 ∧
      |Jrate ϑ (u * ϑ) - (-(1 / 2) * Real.log (u ^ 2 * (1 - u ^ 2 / 4)))| ≤ C * ϑ ^ 2 := by sorry

end GraphNNSphere
