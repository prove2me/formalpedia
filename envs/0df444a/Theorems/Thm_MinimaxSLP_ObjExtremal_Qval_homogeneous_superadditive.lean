-- Prove2me | Theorems.Thm_MinimaxSLP_ObjExtremal_Qval_homogeneous_superadditive
-- name    : MinimaxSLP.ObjExtremal.Qval_homogeneous_superadditive
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T01:15:26.405649+00:00
-- url     : https://prove2.me/theorems/3dd2fc3b-289d-48e7-8783-2480a0b87b9d
-- title:
--   Proof of Theorem 2.2, p. 586 — $\mathcal Q(tq,x)=t\,\mathcal Q(q,x)$ for $t>0$ and $\mathcal Q(a+b,x)\ge\mathcal Q(a,x)+\mathcal Q(b,x)$
-- statement:
--   Let $x$ be such that $X(x)\neq\emptyset$, and assume $\{p : W'p\le q\}\neq\emptyset$ for all $q\in\mathbb R^d$ (Assumption 3). Then the second-stage value $\mathcal Q(q,x)=\min\{q'w : w\in X(x)\}$ is positively homogeneous and superadditive in $q$:
--
--   1. $\mathcal Q(tq,x)=t\,\mathcal Q(q,x)$ for every $t>0$ and $q\in\mathbb R^d$;
--   2. for all $a,b\in\mathbb R^d$,
--   $$
--   \mathcal Q(a+b,x)\ \ge\ \mathcal Q(a,x)+\mathcal Q(b,x).
--   $$
--
--   In the proof of Theorem 2.2 these give $\mathcal Q\big(v_k/v_{k0}+r_k/\sqrt\epsilon,x\big)\ge\mathcal Q(v_k/v_{k0},x)+\mathcal Q(r_k,x)/\sqrt\epsilon$.
--
--   **Formalization Note** The paper's display is the case $a=v_k/v_{k0}$, $b=r_k/\sqrt\epsilon$; the statement here is the general form.
-- source:
--   Bertsimas, Doan, Natarajan & Teo, Models for Minimax Stochastic Linear Optimization Problems with Risk Aversion, Math. Oper. Res. 35(3), 2010, p. 586, proof of Theorem 2.2

import Mathlib
import Definitions.Def_MomentDRO_Conf_Setting
import Definitions.Def_MinimaxSLP_ObjExtremal_Model

open MeasureTheory Matrix Filter Topology

namespace MinimaxSLP.ObjExtremal

/-- Proof of Theorem 2.2 (p. 586): `𝒬(·, x)` is positively homogeneous,
`𝒬(t q, x) = t 𝒬(q, x)` for `t > 0`, and superadditive,
`𝒬(a + b, x) ≥ 𝒬(a, x) + 𝒬(b, x)` (the paper's display is the case
`a = v_k/v_k0`, `b = r_k/√ε`). -/
theorem Qval_homogeneous_superadditive {n r d : ℕ}
    (W : Matrix (Fin r) (Fin d) ℝ) (T : Matrix (Fin r) (Fin n) ℝ) (h : Fin r → ℝ)
    (hA3 : ∀ q : Fin d → ℝ, ∃ π : Fin r → ℝ, Wᵀ *ᵥ π ≤ q)
    (x : Fin n → ℝ) (hrec : (MinimaxSLP.ObjSDP.recourseSet W T h x).Nonempty) :
    (∀ t : ℝ, 0 < t → ∀ q : Fin d → ℝ, MinimaxSLP.ObjSDP.Qval W T h (t • q) x = t * MinimaxSLP.ObjSDP.Qval W T h q x) ∧
    ∀ a c : Fin d → ℝ, MinimaxSLP.ObjSDP.Qval W T h a x + MinimaxSLP.ObjSDP.Qval W T h c x ≤ MinimaxSLP.ObjSDP.Qval W T h (a + c) x := by sorry

end MinimaxSLP.ObjExtremal
