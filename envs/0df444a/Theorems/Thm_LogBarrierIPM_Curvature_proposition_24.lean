-- Prove2me | Theorems.Thm_LogBarrierIPM_Curvature_proposition_24
-- name    : LogBarrierIPM.Curvature.proposition_24
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T01:31:38.229322+00:00
-- url     : https://prove2.me/theorems/ab701a55-c011-4f7f-9b69-28f969a81b14
-- title:
--   Proposition 24 — $\liminf_t\kappa(\mathcal C_t,[t^{\lambda_0},t^{\lambda_p}])$ is at least the sum of the weak tropical angles $\angle^*$ along $\mathcal C^{\mathrm{trop}}$
-- statement:
--   Let $\mathrm{LP}(\mathbf A,\mathbf b,\mathbf c)$ be a linear program over the Puiseux field $\mathbb K$, with $\mathbf A\in\mathbb K^{m\times n}$, $\mathbf b\in\mathbb K^m$, $\mathbf c\in\mathbb K^n$, and let $\mathcal C_t$ be the primal-dual central path $\mu\mapsto(x^\mu,w^\mu,s^\mu,y^\mu)\in\mathbb R^{2N}$ of the real linear program $\mathrm{LP}(\mathbf A(t),\mathbf b(t),\mathbf c(t))$, for every sufficiently large $t$. Let $\underline\lambda,\overline\lambda\in\mathbb R$ and $\underline\lambda=\lambda_0<\lambda_1<\dots<\lambda_{p-1}<\lambda_p=\overline\lambda$, and let $\mathcal C^{\mathrm{trop}}(\lambda_k)=\mathrm{val}(\mathbf z_k)$, where $\mathbf z_k$ is the point of the central path of $\mathrm{LP}(\mathbf A,\mathbf b,\mathbf c)$ over $\mathbb K$ with parameter $t^{\lambda_k}$. Then
--   $$\liminf_{t\to\infty}\kappa\big(\mathcal C_t,[t^{\underline\lambda},t^{\overline\lambda}]\big)\ \ge\ \sum_{k=1}^{p-1}\angle^*\,\mathcal C^{\mathrm{trop}}(\lambda_{k-1})\,\mathcal C^{\mathrm{trop}}(\lambda_k)\,\mathcal C^{\mathrm{trop}}(\lambda_{k+1}).$$
--
--   This is the bridge from the combinatorics of the tropical central path to a lower bound on the total curvature of the classical central paths.
--
--   **Formalization Note** The statement quantifies over every family $\mathcal C_t$ that solves system (1) for $A(t),b(t),c(t)$ and every $\mu>0$, for all large $t$, and over every family $\mathbf z_0,\dots,\mathbf z_p$ of central-path points over $\mathbb K$ with parameters $t^{\lambda_k}$ (encoded through evaluations, see the definition `PuiseuxLP`); the central path over $\mathbb K$ is unique, so $\mathrm{val}(\mathbf z_k)$ is the tropical central path at $\lambda_k$. The total curvature is the `EReal`-valued $\kappa$ and the $\liminf$ is taken in `EReal`. The turning angles of $\mathcal C_t$ are taken in $\mathbb R^{2N}$ with blocks in the order $(x,w,s,y)$.
-- source:
--   Allamigeon, Benchimol, Gaubert, Joswig, Log-Barrier Interior Point Methods Are Not Strongly Polynomial, arXiv:1708.01544v2, p. 22, Proposition 24

import Mathlib
import Definitions.Def_LogBarrierIPM_Curvature_TotalCurvature
import Definitions.Def_LogBarrierIPM_Curvature_SlackCentralPath
import Definitions.Def_LogBarrierIPM_Curvature_Puiseux
import Definitions.Def_LogBarrierIPM_Curvature_TropicalAngle
import Definitions.Def_LogBarrierIPM_Curvature_PuiseuxLP

open Filter Topology

namespace LogBarrierIPM.Curvature

/-- Proposition 24 (p. 22). Let `LP(A, b, c)` be a Puiseux linear program, `C_t` the primal-dual
central path of the real linear program `LP(A(t), b(t), c(t))` (for all sufficiently large `t`),
and `λ_0 < λ_1 < ⋯ < λ_p`. If `Z_k` is the point of the central path of `LP(A, b, c)` over `𝕂`
with parameter `t^{λ_k}`, so that `C^trop(λ_k) = val(Z_k)`, then
`liminf_{t→∞} κ(C_t, [t^{λ_0}, t^{λ_p}]) ≥ ∑_{k=1}^{p-1} ∠* C^trop(λ_{k−1}) C^trop(λ_k) C^trop(λ_{k+1})`. -/
theorem proposition_24 {m n : ℕ} (A : Matrix (Fin m) (Fin n) Puiseux) (b : Fin m → Puiseux)
    (c : Fin n → Puiseux) (p : ℕ) (lam : ℕ → ℝ) (hlam : ∀ k : ℕ, k < p → lam k < lam (k + 1))
    (Z : ℕ → PuiseuxSlackPoint n m)
    (hZ : ∀ k : ℕ, k ≤ p → IsPuiseuxCentralPathPoint A b c (lam k) (Z k))
    (C : ℝ → ℝ → SlackPoint n m)
    (hC : ∀ᶠ t in atTop, ∀ μ : ℝ, 0 < μ →
      IsSlackCentralPathPoint (evalMatrix A t) (evalFun b t) (evalFun c t) μ (C t μ)) :
    (((∑ k ∈ Finset.range (p - 1),
        weakTropicalAngle (valPoint (Z k)) (valPoint (Z (k + 1))) (valPoint (Z (k + 2))) : ℝ)) :
        EReal) ≤
      liminf (fun t : ℝ => totalCurvature (fun μ => primalDualPoint (C t μ))
        (Set.Icc (t ^ lam 0) (t ^ lam p))) atTop := by sorry

end LogBarrierIPM.Curvature
