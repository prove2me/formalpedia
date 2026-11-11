-- Prove2me | Theorems.Thm_NetUnrelDesign_Main_eq_2_2
-- name    : NetUnrelDesign.Main.eq_2_2
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T02:09:37.789201+00:00
-- url     : https://prove2.me/theorems/1396871d-e6a8-4a55-9116-9e7ebc294c1c
-- title:
--   Section 2.2, eq. (2.2) — the relative comparison ⟨∇log u(x), x − y⟩ ≥ (1 − u(x))(1 − u(y)/u(x))
-- statement:
--   Let $(G,q^0)$ be the paper's network: connected, $n\ge2$, $0<q^0_e\le1$. Edge $e$ fails independently with probability $q^0_ee^{-x_e}$, and $u(x)$ is the probability of disconnection. For designs $x,y\ge0$ with $u(y)\le u(x)<1$,
--   $$\langle\nabla\log u(x),\,x-y\rangle\ \ge\ (1-u(x))\Bigl(1-\frac{u(y)}{u(x)}\Bigr).$$
--
--   Differences from the source:
--
--   - encoding: G is the paper's network (standing assumption of §1: connected, n ≥ 2) → hypotheses 2 ≤ n and IsConnectedGraph ends; reason: the paper's graph always satisfies them; no instance of the source is excluded
--   - encoding: ⟨∇log u(x), x − y⟩ → fderiv ℝ (log ∘ u) x (x − y); reason: u(x) > 0 for every design (all edges failing has positive probability and disconnects), so log ∘ u is differentiable at x and its Fréchet derivative applied to x − y is the inner product with the gradient
--   - encoding: "our design variables" → hypotheses x, y ≥ 0 coordinatewise; reason: designs are x ∈ ℝ^m_+ (1.1)
-- source:
--   Sun 2026, Fast Approximation Algorithms for Minimizing Network Unreliability, doi:10.5281/zenodo.23914978 (PDF sha256 1120f100…), Section 2.2, eq. (2.2), p. 7 (PDF 8)

import Mathlib
import Definitions.Def_NetUnrelDesign_Main_Model

open scoped BigOperators

namespace NetUnrelDesign.Main

/-- **Section 2.2, eq. (2.2) (relative comparison).** For the network `(G, q⁰)` (connected,
`n ≥ 2`, `0 < q⁰_e ≤ 1`) and designs `x, y ≥ 0` with `u(y) ≤ u(x) < 1`,
`⟨∇ log u(x), x − y⟩ ≥ (1 − u(x))(1 − u(y)/u(x))`. The inner product with the gradient is the
Fréchet derivative of `log u` at `x` applied to `x − y`. Sun 2026, p. 7 (PDF 8). -/
theorem eq_2_2 {n m : ℕ} (ends : Ends n m) (q0 : Fin m → ℝ) (hst : NetStanding ends q0)
    (x y : Fin m → ℝ) (hx : ∀ e, 0 ≤ x e) (hy : ∀ e, 0 ≤ y e)
    (hle : risk ends q0 y ≤ risk ends q0 x) (hlt : risk ends q0 x < 1) :
    (1 - risk ends q0 x) * (1 - risk ends q0 y / risk ends q0 x) ≤
      fderiv ℝ (fun x' => Real.log (risk ends q0 x')) x (x - y) := by sorry

end NetUnrelDesign.Main
