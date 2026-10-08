-- Prove2me | Theorems.Thm_LeiBR_Sync_prop_4
-- name    : LeiBR.Sync.prop_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T17:10:52.181338+00:00
-- url     : https://prove2.me/theorems/69a62426-d8e3-4eb7-82ae-5408ca1dde42
-- title:
--   Proposition 4 — geometric rate $u_k\le\sqrt N(C+D)q^k$ of Algorithm 1 with $\alpha_{i,k}=\eta^{k+1}$
-- statement:
--   Assume Assumptions 1 and 2, $\mu>0$, and let $x^*$ be a Nash equilibrium. Run Algorithm 1 (abstract form) from a deterministic $x_0\in X$ with $\|x_{i,0}-x_i^*\|\le C$ for all $i$, and with $\alpha_{i,k}=\eta^{k+1}$ for some $\eta\in(0,1)$. Let $a=\|\Gamma\|$, $c=\max\{a,\eta\}$, $q\in(c,1)$ and
--   $$D=\frac{1}{\ln\big((q/c)^e\big)}=\frac1{e\ln(q/c)} .$$
--   Then, with $u_k$ the mean Euclidean norm of the vector of block errors (18),
--   $$u_k\le\sqrt N\,(C+D)\,q^k\qquad\forall k\ge0 .$$
--
--   The inexact scheme thus keeps a linear rate, arbitrarily close to $\max\{a,\eta\}$, and the number of players enters only through the constant.
--
--   **Formalization Note** The initial point is deterministic, as in Algorithm 1 ("Let $y_{i,0}=x_{i,0}\in X_i$"), so $\mathbb E\|x_{i,0}-x_i^*\|\le C$ reads $\|x_{i,0}-x_i^*\|\le C$; the proof's step $u_0\le\sqrt N C$ needs this.
-- source:
--   Lei, Shanbhag, Pang & Sen, On Synchronous, Asynchronous, and Randomized Best-Response Schemes for Stochastic Nash Games, arXiv:1704.04578v2, p. 9, Proposition 4, (18)–(19)

import Mathlib
import Definitions.Def_LeiBR_Sync_NashGame
import Definitions.Def_LeiBR_Sync_StochGame
import Definitions.Def_LeiBR_Sync_Algorithm1

open MeasureTheory

namespace LeiBR.Sync

/-- Proposition 4, p. 9 (geometric rate): for Algorithm 1 with `α_{i,k} = η^{k+1}`,
`η ∈ (0, 1)`, and a deterministic initial point with `‖x_{i,0} - x*_i‖ ≤ C`, put `a = ‖Γ‖`,
`c = max{a, η}`, `q ∈ (c, 1)` and `D = 1/ln((q/c)^e) = 1/(e ln(q/c))`. Then
`u_k = E‖(‖x_{i,k} - x*_i‖)_i‖ ≤ √N (C + D) q^k` for all `k ≥ 0`. -/
theorem prop_4
    {N : ℕ} {n : Fin N → ℕ} {Ω : Type*} [mΩ : MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] {d : ℕ} (ξ : Ω → EuclideanSpace ℝ (Fin d))
    (X : ∀ i : Fin N, Set (Strat n i)) (ψ : Fin N → Profile n → EuclideanSpace ℝ (Fin d) → ℝ)
    (gψ : ∀ i : Fin N, Profile n → EuclideanSpace ℝ (Fin d) → Strat n i) (M : Fin N → ℝ)
    (hA1 : Assumption1 P ξ X ψ gψ M) (μ : ℝ) (hμ : 0 < μ)
    (hA2 : Assumption2 X (payoff P ξ ψ) μ)
    (xhat : Profile n → Profile n) (hxhat : IsProxBR X (payoff P ξ ψ) μ xhat)
    (xs : Profile n) (hxs : IsNashEq X (payoff P ξ ψ) xs)
    (F : Filtration ℕ mΩ) (η : ℝ) (hη0 : 0 < η) (hη1 : η < 1)
    (x0 : Profile n) (x : ℕ → Ω → Profile n)
    (hx : IsAlg1 P F X xhat (fun _ k => η ^ (k + 1)) x0 x)
    (C : ℝ) (hC : ∀ i : Fin N, ‖x0 i - xs i‖ ≤ C)
    (q : ℝ) (hcq : max (specNorm (Gamma X (payoff P ξ ψ) μ)) η < q) (hq1 : q < 1)
    (D : ℝ) (hD : D = 1 / (Real.exp 1 *
      Real.log (q / max (specNorm (Gamma X (payoff P ξ ψ) μ)) η))) :
    ∀ k : ℕ, ∫ ω, blockDist (x k ω) xs ∂P ≤ Real.sqrt N * (C + D) * q ^ k := by sorry

end LeiBR.Sync
