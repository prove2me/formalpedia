-- Prove2me | Theorems.Thm_NonconvexDRS_Tight_thm_4_7_p1_p3
-- name    : NonconvexDRS.Tight.thm_4_7_p1_p3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T15:36:59.081619+00:00
-- url     : https://prove2.me/theorems/48288f4a-7aa9-44dd-961d-0534d5e76a63
-- title:
--   Proof of Theorem 4.7, p. 16 — the example (4.12) with φ₂ = δ_{±1} satisfies 4.7.p1–p3, and ±1 are global minimizers
-- statement:
--   Let $L>0$, $\sigma\in[-L,L]$ and $t>1$. Let $\varphi_1:\mathbb R\to\mathbb R$ be the function (4.12),
--   $$\varphi_1(x)=\begin{cases}\tfrac L2x^2 & \text{if } x\le t,\\ \tfrac L2x^2-\tfrac{L-\sigma}2(x-t)^2 & \text{otherwise,}\end{cases}$$
--   and let $\varphi_2=\delta_{\{\pm1\}}$ be the indicator of $\{-1,1\}$. Then
--
--   1. $\varphi_1$ is $L$-smooth and $\sigma$-hypoconvex (property 4.7.p1);
--   2. $\varphi_2$ is proper and lower semicontinuous (4.7.p2);
--   3. $\operatorname{arg\,min}(\varphi_1+\varphi_2)\neq\emptyset$ (4.7.p3); in fact both $-1$ and $1$ are global minimizers of $\varphi_1+\varphi_2$.
--
--   Verbatim (p. 16): "Fix $t>1$, and let $\varphi=\varphi_1+\varphi_2$, where $\varphi_2=\delta_{\{\pm1\}}$ and [(4.12)]. Notice that $\operatorname{dom}\varphi=\{\pm1\}$, and therefore $\pm1$ are the unique stationary points of $\varphi$ (in fact, they are also global minimizers). It can be easily verified that $\varphi_1$ and $\varphi_2$ satisfy properties 4.7.p1, 4.7.p2 and 4.7.p3."
--
--   This is the first step of the counterexample showing that the stepsize bound $\gamma<1/L$ cannot be relaxed: the pair satisfies every requirement of Assumption I.
--
--   **Formalization Note** The functions live on $\mathbb R$, as in the paper's construction. The claim about stationary points is not stated; the global-minimizer claim is.
-- source:
--   Themelis & Patrinos, Douglas-Rachford splitting and ADMM for nonconvex optimization: tight convergence results, arXiv:1709.05747v4, p. 16, proof of Theorem 4.7, (4.12) and properties 4.7.p1–p3

import Mathlib
import Definitions.Def_NonconvexDRS_Tight_Setting
open Filter Topology

namespace NonconvexDRS.Tight

theorem thm_4_7_p1_p3 (L σ t : ℝ) (hL : 0 < L) (hσ : -L ≤ σ ∧ σ ≤ L) (ht : 1 < t) :
    (IsLSmooth (phi1Ex L σ t) L ∧ IsHypoconvex (phi1Ex L σ t) σ) ∧
    (IsProper (indic ({-1, 1} : Set ℝ)) ∧ LowerSemicontinuous (indic ({-1, 1} : Set ℝ))) ∧
    (∃ xs : ℝ, ∀ x : ℝ, (phi1Ex L σ t xs : EReal) + indic {-1, 1} xs ≤
      (phi1Ex L σ t x : EReal) + indic {-1, 1} x) ∧
    (∀ xs ∈ ({-1, 1} : Set ℝ), ∀ x : ℝ, (phi1Ex L σ t xs : EReal) + indic {-1, 1} xs ≤
      (phi1Ex L σ t x : EReal) + indic {-1, 1} x) := by sorry

end NonconvexDRS.Tight
