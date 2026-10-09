-- Prove2me | Theorems.Thm_KAdaptability_PolicyCount_ec1_objective
-- name    : KAdaptability.PolicyCount.ec1_objective
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T08:05:31.038342+00:00
-- url     : https://prove2.me/theorems/2afc6125-fbb7-4d36-bc12-b8d18deefbeb
-- title:
--   Proof of Theorem 1, (EC.1), p. ec1 — min-max reformulation of the objective of 𝒫𝒪_K
-- statement:
--   For every decision $(x,y^1,\dots,y^K)$ (feasible or not), the objective of $\mathcal{PO}_K$ can be rewritten with a randomization over the policies and the order of maximum and minimum exchanged:
--
--   $$\max_{\xi\in\Xi}\Big[\xi^\top Cx+\min_{k\in\mathcal K}\xi^\top Qy^k\Big]\;=\;\min_{\lambda\in\Delta_K}\ \max_{\xi\in\Xi}\Big[\xi^\top Cx+\sum_{k\in\mathcal K}\lambda_k\cdot\xi^\top Qy^k\Big],$$
--
--   where $\Delta_K$ is the unit simplex in $\mathbb R^K$. Taking the infimum over the feasible decisions turns $\mathcal{PO}_K$ into problem (EC.1).
--
--   This identity uses that $\Xi$ is a nonempty compact convex set and that the bracket is linear in $\xi$ and in $\lambda$.
--
--   **Formalization Note** Both sides are in `EReal`; maximum and minimum are read as supremum and infimum. For $K=0$ both sides are $+\infty$.
-- source:
--   Hanasusanto, Kuhn, Wiesemann, K-Adaptability in Two-Stage Robust Binary Programming, preprint, Optimization Online 2014/03/4294 (revision of 2015-03-30), p. ec1 (PDF p. 35), Proof of Theorem 1, reformulation leading to (EC.1)

import Mathlib
import Definitions.Def_KAdaptability_PolicyCount_Mixed

open Matrix

namespace KAdaptability.PolicyCount

variable {N M L nQ R : ℕ}

/-- Proof of Theorem 1, (EC.1), p. ec1: for every decision `(x, y¹, …, y^K)`, the objective of
𝒫𝒪_K equals the infimum over `λ ∈ Δ_K` of `sup_{ξ∈Ξ} [ξ⊤Cx + Σ_k λ_k ξ⊤Qy^k]` (the min-max
exchange). -/
theorem ec1_objective (P : Problem N M L nQ R) (K : ℕ) (x : Fin N → ℝ)
    (ys : Fin K → Fin M → ℝ) :
    P.objPOK K x ys = ⨅ (lam : Fin K → ℝ) (_ : lam ∈ stdSimplex ℝ (Fin K)),
      P.objMixed K x ys lam := by sorry

end KAdaptability.PolicyCount
