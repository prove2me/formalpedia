-- Prove2me | Theorems.Thm_MinimaxSLP_RhsSDP_Qval_eq_max_extreme_points
-- name    : MinimaxSLP.RhsSDP.Qval_eq_max_extreme_points
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T01:16:33.854768+00:00
-- url     : https://prove2.me/theorems/48a47de7-b64d-4ab9-8eef-773eb055d4c9
-- title:
--   Proof of Theorem 3.2, p. 589 — 𝒬(h, x) = max over the dual extreme points of (h − Tx)′p_i
-- statement:
--   Let $W\in\mathbb R^{r\times d}$, $T\in\mathbb R^{r\times n}$ and $q\in\mathbb R^d$ satisfy complete recourse, $\{Ww : w\ge 0\}=\mathbb R^r$ (Assumption 2), and $\{p : W'p\le q\}\neq\emptyset$ (Assumption 3 at the constant $q$), and let $p_1,\dots,p_N$ be exactly the extreme points of $\{p : W'p\le q\}$ (Assumption 5). Then for every $x\in\mathbb R^n$ and every $h\in\mathbb R^r$,
--   $$
--   \mathcal Q(h,x)=\max_{i=1,\dots,N}(h-Tx)'p_i ,
--   $$
--   and the maximum is attained; in particular $N\ge 1$.
--
--   This replaces the second-stage linear program by a maximum of finitely many affine functions of $h$, which turns each dual constraint into finitely many quadratic inequalities.
--
--   **Formalization Note** The conclusion is `IsGreatest` of the finite set $\{(h-Tx)'p_i\}$ at $\mathcal Q(h,x)$, the real supremum over the dual polyhedron; this also forces the list of extreme points to be nonempty, so $N\ge 1$ is a consequence, not a hypothesis.
-- source:
--   Bertsimas, Doan, Natarajan & Teo, Models for Minimax Stochastic Linear Optimization Problems with Risk Aversion, Math. Oper. Res. 35(3), 2010, p. 589, proof of Theorem 3.2 (first display); Assumption 5, p. 589

import Mathlib
import Definitions.Def_MomentDRO_Conf_Setting
import Definitions.Def_WorstCaseVaR_KnownMoments_Basic
import Definitions.Def_MinimaxSLP_RhsSDP_Model

namespace MinimaxSLP.RhsSDP

open MeasureTheory Matrix

/-- Proof of Theorem 3.2, p. 589: under complete recourse (Assumption 2), dual feasibility at
the constant `q` (Assumption 3) and Assumption 5 (`p_1, …, p_N`, here `ps`, are exactly the
extreme points of `{π : W′π ≤ q}`), for every `x ∈ ℝⁿ` and `h ∈ ℝʳ` the second-stage value is
the largest of the `(h − T x)′p_i`: `𝒬(h, x) = max_{i} (h − T x)′p_i`, the maximum being
attained (`IsGreatest` of the finite range, which in particular forces `N ≥ 1`). -/
theorem Qval_eq_max_extreme_points {r d n N : ℕ}
    (W : Matrix (Fin r) (Fin d) ℝ) (T : Matrix (Fin r) (Fin n) ℝ) (q : Fin d → ℝ)
    (ps : Fin N → Fin r → ℝ)
    (hA2 : ∀ z : Fin r → ℝ, ∃ w : Fin d → ℝ, 0 ≤ w ∧ W *ᵥ w = z)
    (hA3 : ∃ π : Fin r → ℝ, Wᵀ *ᵥ π ≤ q)
    (hA5 : Set.range ps = Set.extremePoints ℝ {π : Fin r → ℝ | Wᵀ *ᵥ π ≤ q})
    (x : Fin n → ℝ) (h : Fin r → ℝ) :
    IsGreatest (Set.range fun i : Fin N => (h - T *ᵥ x) ⬝ᵥ ps i) (Qval W T q h x) := by sorry

end MinimaxSLP.RhsSDP
