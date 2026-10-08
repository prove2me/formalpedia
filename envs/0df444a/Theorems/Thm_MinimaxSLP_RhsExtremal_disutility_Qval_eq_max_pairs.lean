-- Prove2me | Theorems.Thm_MinimaxSLP_RhsExtremal_disutility_Qval_eq_max_pairs
-- name    : MinimaxSLP.RhsExtremal.disutility_Qval_eq_max_pairs
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T02:17:01.058513+00:00
-- url     : https://prove2.me/theorems/82368608-2eb2-47c2-86e3-77f0bde74d21
-- title:
--   Proof of Theorem 3.3, p. 590 — 𝕌(𝒬(h, x)) = max over pairs (k, i) of α_k(h − Tx)′p_i + β_k
-- statement:
--   Let $W\in\mathbb R^{r\times d}$, $T\in\mathbb R^{r\times n}$ and $q\in\mathbb R^d$ satisfy complete recourse, $\{Ww : w\ge 0\}=\mathbb R^r$ (Assumption 2), and dual feasibility, $\{p\in\mathbb R^r : W'p\le q\}\neq\emptyset$ (Assumption 3 at the constant $q$). Let $p_1,\dots,p_N$ be the extreme points of $\{p : W'p\le q\}$ (Assumption 5), and let $\alpha_k\ge 0$ for $k=1,\dots,K$. Then for every $x\in\mathbb R^n$ and every $h\in\mathbb R^r$,
--   $$
--   \mathcal Q(h,x)=\max_{i=1,\dots,N}(h-Tx)'p_i,\qquad \mathbb U(\mathcal Q(h,x))=\max_{k=1,\dots,K}(\alpha_k\mathcal Q(h,x)+\beta_k)=\max_{k=1,\dots,K,\ i=1,\dots,N}\big(\alpha_k(h-Tx)'p_i+\beta_k\big),
--   $$
--   and both maxima are attained.
--
--   This identity turns the expected disutility into a maximum of finitely many affine functions of $h$, which is what makes the dual (16) and the extremal distribution possible.
--
--   **Formalization Note** Both maxima are stated as `IsGreatest` of the finite range, which also forces $N\ge 1$. $\mathcal Q(h,x)$ is the real supremum of $(h-Tx)'p$ over the dual polyhedron.
-- source:
--   Bertsimas, Doan, Natarajan & Teo, Models for Minimax Stochastic Linear Optimization Problems with Risk Aversion, Math. Oper. Res. 35(3), 2010, p. 590, proof of Theorem 3.3 (first display); with p. 589, proof of Theorem 3.2

import Mathlib
import Definitions.Def_MomentDRO_Conf_Setting
import Definitions.Def_MinimaxSLP_RhsExtremal_Model

namespace MinimaxSLP.RhsExtremal

open MeasureTheory Matrix

/-- Proof of Theorem 3.3, p. 590: under complete recourse (Assumption 2), dual feasibility at the
constant `q` (Assumption 3), Assumption 5 (`p_1, …, p_N` are the extreme points of
`{π : W′π ≤ q}`) and `α_k ≥ 0`, for every `h ∈ ℝʳ` the second-stage value is the largest of the
`(h − T x)′p_i`, and `𝕌(𝒬(h, x)) = max_{k, i} (α_k (h − T x)′p_i + β_k)`; both maxima are attained
(`IsGreatest` of the finite range). -/
theorem disutility_Qval_eq_max_pairs {r d n K N : ℕ} [NeZero K]
    (W : Matrix (Fin r) (Fin d) ℝ) (T : Matrix (Fin r) (Fin n) ℝ) (q : Fin d → ℝ)
    (α β : Fin K → ℝ) (ps : Fin N → Fin r → ℝ)
    (hα : ∀ k, 0 ≤ α k)
    (hA2 : ∀ z : Fin r → ℝ, ∃ w : Fin d → ℝ, 0 ≤ w ∧ W *ᵥ w = z)
    (hA3 : ∃ π : Fin r → ℝ, Wᵀ *ᵥ π ≤ q)
    (hA5 : Set.range ps = Set.extremePoints ℝ {π : Fin r → ℝ | Wᵀ *ᵥ π ≤ q})
    (x : Fin n → ℝ) (h : Fin r → ℝ) :
    IsGreatest (Set.range fun i : Fin N => (h - T *ᵥ x) ⬝ᵥ ps i) (MinimaxSLP.RhsSDP.Qval W T q h x) ∧
    IsGreatest (Set.range fun ki : Fin K × Fin N => α ki.1 * ((h - T *ᵥ x) ⬝ᵥ ps ki.2) + β ki.1)
      (MinimaxSLP.ObjSDP.disutility α β (MinimaxSLP.RhsSDP.Qval W T q h x)) := by sorry

end MinimaxSLP.RhsExtremal
