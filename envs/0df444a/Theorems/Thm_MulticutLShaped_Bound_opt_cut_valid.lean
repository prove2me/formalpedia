-- Prove2me | Theorems.Thm_MulticutLShaped_Bound_opt_cut_valid
-- name    : MulticutLShaped.Bound.opt_cut_valid
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-04T08:15:23.410898+00:00
-- url     : https://prove2.me/theorems/617ad39d-afec-4b6a-abea-c6cde89ebe88
-- title:
--   Section 4, p. 387 — each cut (15)–(16) is a supporting affine minorant of $p_kQ_k$ (outer linearization)
-- statement:
--   Let $\pi$ be the multiplier of a basis that is simplex-optimal for Problem $k$ of type (7) at a first-stage point $x'$, and let $(E,e)=(p_k\pi T_k,\ p_k\pi h_k)$ be the optimality cut (15)–(16) it generates. Then for **every** $x\in\mathbb R^{n_1}$,
--   $$e - E x \;=\; p_k\,\pi\,(h_k - T_k x)\ \le\ p_k\,Q_k(x),\qquad Q_k(x)=\min\{q_k y\mid Wy=h_k-T_kx,\ y\ge 0\},$$
--   with equality at $x=x'$.
--
--   So each cut of scenario $k$ is an affine minorant of $p_kQ_k$ that touches it at the point where it was generated: the multicut algorithm outer-linearizes every $Q_k$ (Eq. (10)) instead of $\Omega=\sum_k p_kQ_k$.
--
--   **Formalization Note** $Q_k(x)$ is extended-real valued ($+\infty$ when infeasible), and the inequality is between extended reals; with $p_k=0$ both sides are $0$.
-- source:
--   Birge and Louveaux, A multicut algorithm for two-stage stochastic linear programs, Eur. J. Oper. Res. 34 (1988), p. 387, Section 4 (with Eq. (10), p. 386, and Eqs. (15)-(16), p. 387)

import Mathlib
import Definitions.Def_StochasticProg_Recourse_Instance
import Definitions.Def_StochasticProg_LShaped_Bases
import Definitions.Def_MulticutLShaped_Bound_Cuts

namespace MulticutLShaped.Bound

open StochasticProg.Recourse StochasticProg.LShaped
open scoped Matrix

theorem opt_cut_valid {n1 n2 m1 m2 K : ℕ} (inst : Instance n1 n2 m1 m2 K) (k : Fin K)
    (b : Basis n2 m2) (x' : Fin n1 → ℝ) (hb : IsSimplexOptimal inst k b x') :
    (∀ x : Fin n1 → ℝ, (((optCut inst k b).2 - (optCut inst k b).1 ⬝ᵥ x : ℝ) : EReal) ≤
      (inst.p k : EReal) * QVal inst x k) ∧
    (((optCut inst k b).2 - (optCut inst k b).1 ⬝ᵥ x' : ℝ) : EReal) =
      (inst.p k : EReal) * QVal inst x' k := by sorry

end MulticutLShaped.Bound
