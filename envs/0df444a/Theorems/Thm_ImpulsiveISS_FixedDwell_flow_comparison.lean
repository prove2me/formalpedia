-- Prove2me | Theorems.Thm_ImpulsiveISS_FixedDwell_flow_comparison
-- name    : ImpulsiveISS.FixedDwell.flow_comparison
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T17:45:14.081317+00:00
-- url     : https://prove2.me/theorems/6b6625db-528e-4363-a8b6-13d2eeb64ccc
-- title:
--   Proof of Theorem 1, p. 7, (3.11) — along a flow piece with D⁺y ≤ −φ(y), F(y(t)) − F(y(a)) ≤ −(t − a)
-- statement:
--   Let $\varphi:\mathbb R_+\to\mathbb R_+$ be positive definite (continuous, $\varphi(s)=0$ iff $s=0$), fix $r>0$ and put
--   $$F(q)=\int_r^q\frac{ds}{\varphi(s)},\qquad q>0.$$
--   Let $a\le b$ and let $y$ be a real function that is continuous and positive on $[a,b]$ and whose upper right Dini derivative satisfies $D^+y(t)\le-\varphi(y(t))$ for every $t\in[a,b)$. Then
--   $$F(y(t))-F(y(a))\le-(t-a)\qquad\text{for all }t\in[a,b].$$
--
--   In the proof of Theorem 1 this is applied to $y=V(x(\cdot))$ on an impulse-free interval $[t_i,t_{i+1})$, where the Lyapunov condition gives (3.8); the closed right end point carries the left limit $y^-(t_{i+1})$, which is how (3.13) follows from (3.11).
--
--   **Formalization Note** The page states the comparison for the specific $y=V(x(\cdot))$ along the trajectory; the statement here is the same step for an arbitrary real function satisfying the same hypotheses, which is all the page's derivation uses. $D^+$ is the referenced `diniUpperRight`, valued in `EReal`. $F$ is the oriented interval integral `Fint φ r`; it is applied only to positive arguments.
-- source:
--   Dashkovskiy and Mironchenko, Input-to-state stability of nonlinear impulsive systems, arXiv:1212.5481v1, p. 7, proof of Theorem 1, (3.10)–(3.12)

import Mathlib
import Definitions.Def_SmallGainISS_Lyapunov_Gains
import Definitions.Def_ProcessingNetworks_LyapunovCriteria_DiniDerivative
import Definitions.Def_ImpulsiveISS_FixedDwell_Setting

open scoped NNReal
open Filter Topology
open SmallGainISS.Lyapunov ProcessingNetworks.LyapunovCriteria

namespace ImpulsiveISS.FixedDwell

/-- (3.10)–(3.11), p. 7: on an impulse-free piece `[a, b]` along which `y > 0` is continuous and
`D⁺y(t) ≤ −φ(y(t))` for `t ∈ [a, b)`, the function `F(q) = ∫_r^q ds/φ(s)` (any fixed `r > 0`)
decreases at least at unit rate: `F(y(t)) − F(y(a)) ≤ −(t − a)` for `t ∈ [a, b]`. -/
theorem flow_comparison (φ : ℝ≥0 → ℝ≥0) (hφ : IsPosDef φ) (r : ℝ) (hr : 0 < r)
    (y : ℝ → ℝ) (a b : ℝ) (hab : a ≤ b) (hcont : ContinuousOn y (Set.Icc a b))
    (hpos : ∀ t ∈ Set.Icc a b, 0 < y t)
    (hD : ∀ t ∈ Set.Ico a b, diniUpperRight y t ≤ ((-(φ (y t).toNNReal : ℝ) : ℝ) : EReal)) :
    ∀ t ∈ Set.Icc a b, Fint φ r (y t) - Fint φ r (y a) ≤ -(t - a) := by sorry

end ImpulsiveISS.FixedDwell
