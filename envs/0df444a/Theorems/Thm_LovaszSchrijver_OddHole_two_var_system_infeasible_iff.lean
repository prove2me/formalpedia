-- Prove2me | Theorems.Thm_LovaszSchrijver_OddHole_two_var_system_infeasible_iff
-- name    : LovaszSchrijver.OddHole.two_var_system_infeasible_iff
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T15:49:53.818988+00:00
-- url     : https://prove2.me/theorems/1facb5a6-4b7f-4676-b56e-4eea424306f6
-- title:
--   Lemma 2.4 — solvability of a system a(ij) ≤ yᵢ + yⱼ ≤ b(ij) via walks
-- statement:
--   Let $H = (W, F)$ be a finite graph, let two values $0 \le a(ij) \le b(ij)$ be associated with each edge $ij \in F$, and let $U \subseteq W$. Then the linear system
--   $$a(ij) \le y_i + y_j \le b(ij)\ (ij \in F), \qquad y_i \ge 0\ (i \in W), \qquad y_i = 0\ (i \in U)$$
--   has no solution $y \in \mathbb{R}^W$ if and only if there exists a walk $v_0, v_1, \dots, v_p$ in $H$ (vertices not necessarily distinct, $v_t v_{t+1} \in F$) such that one of the following holds:
--
--   1. (a) $p$ is odd and $b(v_0v_1) - a(v_1v_2) + b(v_2v_3) - \cdots + b(v_{p-1}v_p) < 0$;
--   2. (b) $p$ is even, $v_0 = v_p$, and $b(v_0v_1) - a(v_1v_2) + b(v_2v_3) - \cdots - a(v_{p-1}v_p) < 0$;
--   3. (c) $p$ is even, $v_p \in U$, and $b(v_0v_1) - a(v_1v_2) + b(v_2v_3) - \cdots - a(v_{p-1}v_p) < 0$;
--   4. (d) $p$ is odd, $v_0, v_p \in U$, and $-a(v_0v_1) + b(v_1v_2) - a(v_2v_3) - \cdots - a(v_{p-1}v_p) < 0$.
--
--   The paper calls this a folklore lemma, "a criterion for the solvability of such a system, more combinatorial than the Farkas lemma". It is applied to the system on the entries of $Y$ in the proof of Theorem 2.3.
--
--   **Formalization Note** Edge values are functions on unordered pairs, so $a(ij) = a(ji)$. In (a)–(c) the alternating sum starts with $+b$ on the first edge and alternates; in (d) it starts with $-a$. The hypothesis $0 \le a \le b$ is stated as printed, although the application in the paper uses lower bounds $x_i + x_j + x_k - 1$ that can be negative.
-- source:
--   Lovász and Schrijver, Cones of matrices and set-functions and 0–1 optimization, SIAM J. Optim. 1(2) (1991), p. 178, Lemma 2.4

import Mathlib
import Definitions.Def_LovaszSchrijver_OddHole_AlternatingWalk

namespace LovaszSchrijver.OddHole

/-- Lemma 2.4 (p. 178): for a finite graph `H = (W, F)` with values `0 ≤ a(ij) ≤ b(ij)` on its
edges and `U ⊆ W`, the system `a(ij) ≤ yᵢ + yⱼ ≤ b(ij)` (ij ∈ F), `yᵢ ≥ 0` (i ∈ W),
`yᵢ = 0` (i ∈ U) has no solution iff there is a walk `v₀, …, v_p` of one of the types
(a)–(d). -/
theorem two_var_system_infeasible_iff {W : Type} [Fintype W] (H : SimpleGraph W)
    (a b : Sym2 W → ℝ) (hab : ∀ e ∈ H.edgeSet, 0 ≤ a e ∧ a e ≤ b e) (U : Finset W) :
    (¬ ∃ y : W → ℝ,
        (∀ i j, H.Adj i j → a s(i, j) ≤ y i + y j ∧ y i + y j ≤ b s(i, j)) ∧
        (∀ i, 0 ≤ y i) ∧ (∀ i ∈ U, y i = 0)) ↔
      ∃ (p : ℕ) (v : Fin (p + 1) → W), IsWalkSeq H v ∧
        ((Odd p ∧ altB a b v < 0) ∨
         (Even p ∧ v 0 = v (Fin.last p) ∧ altB a b v < 0) ∨
         (Even p ∧ v (Fin.last p) ∈ U ∧ altB a b v < 0) ∨
         (Odd p ∧ v 0 ∈ U ∧ v (Fin.last p) ∈ U ∧ altA a b v < 0)) := by sorry

end LovaszSchrijver.OddHole
