-- Prove2me | Theorems.Thm_GhadimiLan_RSG_iterate_measurable
-- name    : GhadimiLan.RSG.iterate_measurable
-- status  : Proved
-- author  : @SamenHossain
-- created : 2026-10-08T22:58:08.788583+00:00
-- url     : https://prove2.me/theorems/04e90283-16ad-40ac-94bf-5964c5c2d5c4
-- title:
--   Proof of Theorem 2.1, p. 7 — the RSG iterate $x_k$ is $\mathcal F_{k-1}$-measurable (a function of the history $\xi_{[k-1]}$)
-- statement:
--   Let $G:\mathbb R^n\times\Xi\to\mathbb R^n$ be a Borel stochastic oracle, let $(\mathcal F_k)_{k\ge0}$ be a filtration on the sample space, and let the noise variables $\xi_k$ be $\mathcal F_k$-measurable for every $k\ge1$. Let $x_1,x_2,\dots$ be an RSG run from the deterministic point $x_1$, i.e.
--   $$x_{k+1}=x_k-\gamma_k\,G(x_k,\xi_k),\qquad k\ge1,$$
--   pointwise on the sample space, with real stepsizes $\gamma_k$. Then for every $k\ge1$ the iterate $x_k$ is $\mathcal F_{k-1}$-measurable:
--   $$x_k\ \text{is a measurable function with respect to}\ \mathcal F_{k-1}.$$
--
--   This is the remark "the search point $x_k$ is a function of the history $\xi_{[k-1]}$ and hence is random" in the proof of Theorem 2.1. It is the measurability input for the conditional-expectation step (2.10), and it applies verbatim to the two-phase and zeroth-order variants of the method, which use the same recursion.
--
--   **Formalization Note** The run is the platform predicate `IsRSGRun`, which fixes $x_1$ and the recursion for $k\ge1$ only; $x_0$ and $\xi_0$ are unconstrained. The statement is about the $\sigma$-algebra $\mathcal F_{k-1}$ of the filtration, written `Measurable[ℱ (k - 1)]`; for $k=1$ it says that the constant $x_1$ is $\mathcal F_0$-measurable. No probability measure is involved.
-- source:
--   Ghadimi & Lan, Stochastic first- and zeroth-order methods for nonconvex stochastic programming, arXiv:1309.5549v1, proof of Theorem 2.1, p. 7 ("Note that the search point x_k is a function of the history ξ_[k−1] of the generated random process and hence is random")

import Mathlib
import Definitions.Def_ConvexOptAlg_SmoothGD_Defs
import Definitions.Def_GhadimiLan_RSG_Model
open MeasureTheory ProbabilityTheory
open scoped InnerProductSpace

namespace GhadimiLan.RSG

/-- Measurability of the RSG iterates (Ghadimi & Lan, arXiv:1309.5549v1, proof of Theorem 2.1,
p. 7: "the search point `x_k` is a function of the history `ξ_[k−1]`"): if the oracle `G` is
Borel and the noise `ξ_k` is `ℱ_k`-measurable for every `k ≥ 1`, then along an RSG run the
iterate `x_k` is `ℱ_{k-1}`-measurable for every `k ≥ 1` (`x_1 = x1` is constant, hence
`ℱ_0`-measurable). -/
theorem iterate_measurable {n : ℕ} {Ξ : Type*} [MeasurableSpace Ξ] (G : E n → Ξ → E n)
    (hG : Measurable (Function.uncurry G))
    {Ω : Type*} [MeasurableSpace Ω] (ℱ : Filtration ℕ ‹MeasurableSpace Ω›) (ξ : ℕ → Ω → Ξ)
    (hξ : ∀ k : ℕ, 1 ≤ k → Measurable[ℱ k] (ξ k))
    (γ : ℕ → ℝ) (x1 : E n) (x : ℕ → Ω → E n) (hx : IsRSGRun G γ x1 ξ x)
    (k : ℕ) (hk : 1 ≤ k) :
    Measurable[ℱ (k - 1)] (x k) := by sorry

end GhadimiLan.RSG
