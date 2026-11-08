-- Prove2me | Theorems.Thm_GraphNNSphere_lemma_2_4
-- name    : GraphNNSphere.lemma_2_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T06:40:14.334133+00:00
-- url     : https://prove2.me/theorems/9da4269f-3b52-4cc0-9041-35306be412f0
-- title:
--   Lemma 2.4 — cap containment
-- statement:
--   Let $\delta(x,q)=\theta$ and let $Y$ be uniform on $C(q,\psi_0)$, where $0<\theta,\psi_0<\pi/2$. Fix a neighbor radius $0<\rho<\pi$.
--
--   1. Suppose that $\cos\theta\cos\psi_0-\cos\rho\ge\tau\sin\theta\sin\psi_0$ for some $\tau>0$. If $0<\tau<1$, then
--   $$P(\delta(x,Y)>\rho)\le\sqrt{d-1}\,(1-\tau^2)^{(d-4)/2}.$$
--   If $\tau\ge1$, this probability is zero.
--   2. If $\cos\theta\cos\psi_0\ge\cos\rho$, then $P(\delta(x,Y)\le\rho)\ge\tfrac12$.
--   3. Consequently, if $\cos\rho\le\cos^2\theta$, then $C(x,\rho)\cap C(q,\theta)$ has at least half the measure of $C(q,\theta)$.
--
--   This controls the fraction of a query cap that lies outside a prescribed neighbor radius.
--
--   Differences from the source:
--   - encoding: Y uniform on C(q, ψ₀) → σ conditioned on the cap (ProbabilityTheory.cond); reason: this is the uniform law on the cap
-- source:
--   Lu, Sharp Limits of Graph-Based Nearest Neighbor Search on the Sphere, STOC 2027 submission (manuscript sha256 93565bc5…), Lemma 2.4, p.17

import Mathlib
import Definitions.Def_GraphNNSphere_unif
import Definitions.Def_GraphNNSphere_cap

open MeasureTheory

namespace GraphNNSphere

/-- Lemma 2.4, cap containment (Lu, *Sharp Limits of Graph-Based Nearest Neighbor Search on the
Sphere*, STOC 2027 submission (manuscript sha256 93565bc5…), Lemma 2.4, p.17).

**Formalization Note** `Y` uniform on `C(q, ψ₀)` is `σ_{d-1}` conditioned on the cap
(`ProbabilityTheory.cond`). The page states no range of `d`, and none is imposed: no `x`, `q` exist
with `0 < θ < π/2` when `d ≤ 1`. The exponent `(d - 4)/2` is real. -/
theorem lemma_2_4 (d : ℕ) (x q : Sph d) (θ ψ₀ ρ : ℝ) (hθ : geo x q = θ) (hθ0 : 0 < θ)
    (hθ1 : θ < Real.pi / 2) (hψ0 : 0 < ψ₀) (hψ1 : ψ₀ < Real.pi / 2) (hρ0 : 0 < ρ)
    (hρ1 : ρ < Real.pi) :
    (∀ τ : ℝ, 0 < τ →
      τ * (Real.sin θ * Real.sin ψ₀) ≤ Real.cos θ * Real.cos ψ₀ - Real.cos ρ →
      (τ < 1 → (ProbabilityTheory.cond (unif d) (cap q ψ₀) {y | ρ < geo x y}).toReal ≤
        Real.sqrt ((d : ℝ) - 1) * (1 - τ ^ 2) ^ (((d : ℝ) - 4) / 2)) ∧
      (1 ≤ τ → ProbabilityTheory.cond (unif d) (cap q ψ₀) {y | ρ < geo x y} = 0)) ∧
    (Real.cos ρ ≤ Real.cos θ * Real.cos ψ₀ →
      1 / 2 ≤ (ProbabilityTheory.cond (unif d) (cap q ψ₀) {y | geo x y ≤ ρ}).toReal) ∧
    (Real.cos ρ ≤ Real.cos θ ^ 2 →
      1 / 2 * (unif d (cap q θ)).toReal ≤ (unif d (cap x ρ ∩ cap q θ)).toReal) := by sorry

end GraphNNSphere
