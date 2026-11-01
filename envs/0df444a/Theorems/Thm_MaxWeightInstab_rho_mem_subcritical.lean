-- Prove2me | Theorems.Thm_MaxWeightInstab_rho_mem_subcritical
-- name    : MaxWeightInstab.rho_mem_subcritical
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T09:15:34.384562+00:00
-- url     : https://prove2.me/theorems/50799e9c-1db3-4740-9ba4-3b1b34a0f3a8
-- title:
--   Display (4) — $\boldsymbol\rho\in\mathcal C$ whenever $r_{\boldsymbol\rho}=a(1+1/\nu)<1$
-- statement:
--   Let $\nu\ge1$ and $a>0$ with
--
--   $$
--   r_{\boldsymbol\rho}=a\left(1+\frac1\nu\right)<1 . \tag{4}
--   $$
--
--   Then the traffic intensity $\boldsymbol\rho$ of (2) lies in the subcritical region $\mathcal C$, the interior of the convex hull of the schedules (3).
--
--   This is the first conclusion of Theorem 1: the network of Figure 1 is subcritical, so any instability of MaxWeight is a failure of the policy, not of the load.
--
--   Differences from the source:
--   - reading: "ρ ∈ 𝒞 whenever r_ρ := a(1 + 1/ν) < 1" → adds a > 0; reason: a is an arrival rate; for a ≤ 0, ρ has nonpositive coordinates and is not in the interior of a hull lying in the nonnegative orthant; (5) implies a > 0
--   - encoding: ν ∈ ℕ with 1/ν → 0 < ν; reason: excludes only the undefined case
--   - encoding: (3) with the factor 1/ν → ν σ_𝒜₀ + Σ_{j≥1} σ_𝒜ⱼ ≤ ν over ℕ (and the same for ℬ); reason: (3) multiplied by ν ≥ 1; same set
-- source:
--   Bramson, D'Auria, Walton, Stability and Instability of the MaxWeight Policy, arXiv:1909.10825v2, display (4), p.3; proof of Theorem 1, p.7

import Mathlib
import Definitions.Def_MaxWeightInstab_rho
import Definitions.Def_MaxWeightInstab_subcriticalRegion
import Definitions.Def_MaxWeightInstab_rRho

namespace MaxWeightInstab

/-- **`ρ ∈ 𝒞` under (4)** (Bramson, D'Auria & Walton, arXiv:1909.10825v2, p.3: "It follows from displays (2) and (3) that ρ ∈ 𝒞 whenever
`r_ρ := a(1 + 1/ν) < 1` (4)"; p.7: "ρ ∈ 𝒞 follows from (4)"). The traffic intensity (2) of the
network of Figure 1 lies in the interior of the convex hull of the schedules (3).

**Formalization Note.** `a > 0` is assumed: `a` is an arrival rate, and for `a ≤ 0` the vector `ρ`
is not in the interior (the hull lies in the nonnegative orthant). `ν ≥ 1` makes `1/ν` meaningful.
Under Theorem 1's (5) both hold. -/
theorem rho_mem_subcritical (J ν : ℕ) (a : ℝ) (hν : 0 < ν) (ha : 0 < a) (h4 : rRho a ν < 1) :
    rho a J ∈ subcriticalRegion J ν := by sorry

end MaxWeightInstab
