-- Prove2me | Theorems.Thm_KurtzProtter91_Integrals_jdelta_continuous
-- name    : KurtzProtter91.Integrals.jdelta_continuous
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T13:06:54.672795+00:00
-- url     : https://prove2.me/theorems/37606d0c-96d4-46ba-83e5-44dc4b4302bc
-- title:
--   Section 2, p. 1039 (after (2.1)) — x ↦ J_δ(x) and x ↦ x − J_δ(x) are Skorohod-continuous, jointly with x
-- statement:
--   Let $\delta\in(0,\infty]$ and let $J_\delta$ be the jump functional (2.1) on $D_{\mathbb R^m}[0,\infty)$. If $x_n\to x$ in the Skorohod topology on $D_{\mathbb R^m}[0,\infty)$, then
--   $$(x_n,J_\delta(x_n))\to(x,J_\delta(x))\quad\text{and}\quad(x_n,x_n-J_\delta(x_n))\to(x,x-J_\delta(x))$$
--   in the Skorohod topology on $D_{\mathbb R^m\times\mathbb R^m}[0,\infty)$.
--
--   The page states that "Lemma 2.1 shows that $x\to J_\delta(x)$ and $x\to x-J_\delta(x)$ are continuous". The statement here is the joint form that the second clause of Lemma 2.1 gives and that the proof of Theorem 2.2 uses (it needs $(X_n,Y_n,J_\delta(Y_n),Y_n^\delta)$ to converge together); it implies continuity of each map.
--
--   **Formalization Note** For $\delta=\infty$, $J_\infty=0$ and the statement reduces to $x_n\to x$. The norm in (2.1) is $|v|=\sum_i|v_i|$.
-- source:
--   Kurtz and Protter, Weak Limit Theorems for Stochastic Integrals and Stochastic Differential Equations, Ann. Probab. 19 (1991), p. 1039, Section 2 (after (2.1))

import Mathlib
import Definitions.Def_KurtzProtter91_Integrals_Skorohod

open Filter Topology
open scoped NNReal ENNReal

namespace KurtzProtter91.Integrals

theorem jdelta_continuous {m : ℕ} (δ : ℝ≥0∞) (hδ : 0 < δ) (xs : ℕ → ℝ≥0 → Fin m → ℝ)
    (x : ℝ≥0 → Fin m → ℝ) (h : SkorohodTendsto xs x) :
    SkorohodTendsto (fun n t => (xs n t, Jdelta δ (xs n) t)) (fun t => (x t, Jdelta δ x t)) ∧
    SkorohodTendsto (fun n t => (xs n t, xs n t - Jdelta δ (xs n) t))
      (fun t => (x t, x t - Jdelta δ x t)) := by sorry

end KurtzProtter91.Integrals
