-- Prove2me | Theorems.Thm_GhadimiLan_RSG_grad_sq_integrable
-- name    : GhadimiLan.RSG.grad_sq_integrable
-- status  : Proved
-- author  : @SamenHossain
-- created : 2026-10-08T23:01:54.750545+00:00
-- url     : https://prove2.me/theorems/f7598a20-e253-4cff-9875-c5cca1e8d4ed
-- title:
--   Proof of Theorem 2.1, p. 7 — under A1, $\|\nabla f(x_k)\|^2$ is integrable along the RSG run
-- statement:
--   Let $f\in\mathcal C^{1,1}_L(\mathbb R^n)$ have gradient $\nabla f$, let $G$ be a Borel stochastic first-order oracle, and let $x_1,x_2,\dots$ be an RSG run
--   $$x_{k+1}=x_k-\gamma_k\,G(x_k,\xi_k),\qquad k\ge1,$$
--   from a deterministic $x_1$ on a probability space, satisfying Assumption A1 with respect to a filtration $(\mathcal F_k)$: the noise is adapted, $G(x_k,\xi_k)$ is integrable with $\mathbb E[G(x_k,\xi_k)\mid\mathcal F_{k-1}]=\nabla f(x_k)$, and $\mathbb E\|G(x_k,\xi_k)-\nabla f(x_k)\|^2\le\sigma^2$. Then for every $k\ge1$,
--   $$\mathbb E\,\|\nabla f(x_k)\|^2<\infty ,$$
--   that is, $\|\nabla f(x_k)\|^2$ is integrable.
--
--   The paper takes expectations of $\|\nabla f(x_k)\|^2$ in (2.11) without comment; this lemma supplies the missing integrability from the recursion, the Lipschitz continuity of $\nabla f$ and the second-moment bound (1.3) on the oracle error. It is the input that makes the cross term $\langle\nabla f(x_k),\delta_k\rangle$ integrable in (2.10) and the sum in (2.11) well defined, and it transfers unchanged to the other stochastic-approximation schemes of the paper.
--
--   **Formalization Note** The hypotheses are those of the platform structure `AssumptionA1` (which also carries $\sigma\ge0$); no stepsize restriction is needed, the bound holds for arbitrary real $\gamma_k$.
-- source:
--   Ghadimi & Lan, Stochastic first- and zeroth-order methods for nonconvex stochastic programming, arXiv:1309.5549v1, proof of Theorem 2.1, Eq. (2.11), p. 7 (integrability of ‖∇f(x_k)‖² is implicit there; the mission description lists this second-moment induction as required infrastructure)

import Mathlib
import Definitions.Def_ConvexOptAlg_SmoothGD_Defs
import Definitions.Def_GhadimiLan_RSG_Model
open MeasureTheory ProbabilityTheory
open scoped InnerProductSpace

namespace GhadimiLan.RSG

/-- Second-moment bound along an RSG run (Ghadimi & Lan, arXiv:1309.5549v1, proof of
Theorem 2.1, p. 7, where `E‖∇f(x_k)‖²` is used; the paper does not state integrability):
for `f ∈ C^{1,1}_L(ℝⁿ)`, a Borel oracle `G` and an RSG run under Assumption A1, `‖∇f(x_k)‖²`
is integrable for every `k ≥ 1`. The proof is an induction along the recursion:
`‖∇f(x_{k+1})‖ ≤ (1 + L|γ_k|)‖∇f(x_k)‖ + L|γ_k|‖δ_k‖` with `‖δ_k‖ ∈ L²` by (1.3), and
`∇f(x_1)` is constant. -/
theorem grad_sq_integrable {n : ℕ} (f : E n → ℝ) (g : E n → E n) (L : ℝ)
    (hf : ConvexOptAlg.SmoothGD.IsBetaSmooth f g L)
    {Ξ : Type*} [MeasurableSpace Ξ] (G : E n → Ξ → E n) (hG : Measurable (Function.uncurry G))
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ℱ : Filtration ℕ ‹MeasurableSpace Ω›) (ξ : ℕ → Ω → Ξ) (σ : ℝ)
    (γ : ℕ → ℝ) (x1 : E n) (x : ℕ → Ω → E n) (hx : IsRSGRun G γ x1 ξ x)
    (hA1 : AssumptionA1 μ ℱ g G ξ x σ) (k : ℕ) (hk : 1 ≤ k) :
    Integrable (fun ω => ‖g (x k ω)‖ ^ 2) μ := by sorry

end GhadimiLan.RSG
