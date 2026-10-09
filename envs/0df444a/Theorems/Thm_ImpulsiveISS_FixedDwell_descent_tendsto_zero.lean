-- Prove2me | Theorems.Thm_ImpulsiveISS_FixedDwell_descent_tendsto_zero
-- name    : ImpulsiveISS.FixedDwell.descent_tendsto_zero
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T17:45:05.329412+00:00
-- url     : https://prove2.me/theorems/5dedcb73-1c18-41ff-a087-a675b8404e71
-- title:
--   Proof of Theorem 1, p. 8 — a positive sequence along which F drops by δ per step tends to 0 (z_r(t_i) → 0)
-- statement:
--   Let $\varphi:\mathbb R_+\to\mathbb R_+$ be positive definite, fix $r>0$ and put $F(q)=\int_r^q ds/\varphi(s)$ for $q>0$. Let $\delta>0$ and let $(z_i)_{i\ge0}$ be a sequence of positive reals with
--   $$F(z_{i+1})\le F(z_i)-\delta\qquad\text{for all }i.$$
--   Then $z_i\to0$ as $i\to\infty$.
--
--   On p. 8 this is the claim $z_r(t_i)=\tilde\beta(r,t_i-t_0)\to0$, which shows that the comparison function $\tilde\beta(r,\cdot)$ built from (3.15) belongs to $\mathcal L$.
--
--   **Formalization Note** The page argues for the specific sequence $z_r(t_i)$, using only that it is positive and that $F$ drops by $\delta$ at each step (its display $\delta\le F(z_r(t_i))-F(z_r(t_{i+1}))$); the statement here is that argument for an arbitrary such sequence. $F$ is the oriented interval integral `Fint φ r`.
-- source:
--   Dashkovskiy and Mironchenko, Input-to-state stability of nonlinear impulsive systems, arXiv:1212.5481v1, p. 8, proof of Theorem 1, the claim z_r(t_i) → 0

import Mathlib
import Definitions.Def_SmallGainISS_Lyapunov_Gains
import Definitions.Def_ProcessingNetworks_LyapunovCriteria_DiniDerivative
import Definitions.Def_ImpulsiveISS_FixedDwell_Setting

open scoped NNReal
open Filter Topology
open SmallGainISS.Lyapunov ProcessingNetworks.LyapunovCriteria

namespace ImpulsiveISS.FixedDwell

/-- p. 8, `z_r(t_i) → 0`: a positive sequence along which `F(q) = ∫_r^q ds/φ(s)` drops by at
least `δ > 0` at every step tends to `0`. -/
theorem descent_tendsto_zero (φ : ℝ≥0 → ℝ≥0) (hφ : IsPosDef φ) (r : ℝ) (hr : 0 < r)
    (δ : ℝ) (hδ : 0 < δ) (z : ℕ → ℝ) (hz : ∀ i, 0 < z i)
    (hdesc : ∀ i, Fint φ r (z (i + 1)) ≤ Fint φ r (z i) - δ) :
    Tendsto z atTop (𝓝 0) := by sorry

end ImpulsiveISS.FixedDwell
