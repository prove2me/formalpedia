-- Prove2me | Theorems.Thm_HuberSNSDP_proposition_1_part_4
-- name    : HuberSNSDP.proposition_1_part_4
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T04:23:32.870382+00:00
-- url     : https://prove2.me/theorems/a6bb29e4-9973-4267-9dfb-ddb0355cda65
-- title:
--   Proposition 1 (part 4) — $\Phi$ is strongly semismooth on $\mathbb R\times\mathbb S^n$
-- statement:
--   The Huber smoothing $\Phi:\mathbb R\times\mathbb S^n\to\mathbb S^n$ is strongly semismooth at every point $y$ of $\mathbb R\times\mathbb S^n$ (Definition 1): $\Phi$ is locally Lipschitz, directionally differentiable at $y$, and
--   $$\|\Phi(y+h)-\Phi(y)-Vh\|=O(\|h\|^2)\quad(h\to0)\qquad\text{for every }V\in\partial\Phi(y+h).$$
--
--   Strong semismoothness gives the order $1+\tau$ of the local convergence in Theorem 3.
--
--   Differences from the source:
--   - encoding: $\mathbb S^n$, $\mathbb R^m$, $\mathbb X=\mathbb S^n\times\mathbb R^m\times\mathbb S^n$ with the trace inner product and Euclidean norms → `SymMat (Fin n)` (Frobenius inner product = trace inner product), `EuclideanSpace ℝ (Fin m)`, `WithLp 2` products; reason: Lean convention; the same spaces, inner products and norms
--   - encoding: Definition 1, p.7 (semismooth at $y$, and $O(\|h\|^2)$ uniformly over $V\in\partial\Theta(y+h)$) → the published `ZeroOneSCO.StronglySemismoothAt11` (locally Lipschitz near $y$, directionally differentiable at $y$, $\exists C,\delta>0$ with the $C\|h\|^2$ bound for $\|h\|<\delta$ and every $V$ in the Clarke Jacobian); reason: the same definition; the $O(\|h\|^2)$ bound implies the $o(\|h\|)$ bound of semismoothness
-- source:
--   Liang, Sun & Toh, A Squared Smoothing Newton Method for Semidefinite Programming, arXiv:2303.05825v4, Proposition 1, part 4, p.10; Definition 1, p.7

import Mathlib
import Definitions.Def_HuberSNSDP_Setting
import Definitions.Def_ZeroOneSCO_Semismooth

open scoped RealInnerProductSpace Topology
open Filter SunNLSDP.Equiv NonsmoothNewton.Shared

namespace HuberSNSDP

/-- Proposition 1, part 4, p.10 (Liang, Sun & Toh, arXiv:2303.05825v4): `Φ` is strongly
semismooth on `ℝ × Sⁿ`, in the sense of Definition 1, p.7.

**Formalization Note.** Definition 1 is the published `ZeroOneSCO.StronglySemismoothAt11`: locally
Lipschitz near the point, directionally differentiable there, and
`‖Φ(y + h) − Φ(y) − Vh‖ ≤ C‖h‖²` for all small `h` and all `V ∈ ∂Φ(y + h)` (Clarke's generalized
Jacobian, the published `clarkeJac`). The `O(‖h‖²)` bound implies the `o(‖h‖)` bound of
semismoothness, so this is "semismooth at `y` and `O(‖h‖²)`". -/
theorem proposition_1_part_4 (n : ℕ) :
    ∀ p : RS (Fin n), ZeroOneSCO.StronglySemismoothAt11 (PhiPair (ι := Fin n)) p := by sorry

end HuberSNSDP
