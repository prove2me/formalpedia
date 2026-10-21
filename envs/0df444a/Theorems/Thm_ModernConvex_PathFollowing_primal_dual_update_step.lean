-- Prove2me | Theorems.Thm_ModernConvex_PathFollowing_primal_dual_update_step
-- name    : ModernConvex.PathFollowing.primal_dual_update_step
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-20T15:34:54.71158+00:00
-- url     : https://prove2.me/theorems/387cf85f-68cd-4ac3-b85b-b9a1765c6f0a
-- title:
--   Theorem 6.5.2 — one primal-dual path-following step for SDP stays strictly feasible and in N_κ
-- statement:
--   Let $k \ge 1$, let $\mathbf S^k$ be the space of real symmetric $k \times k$ matrices with $\langle X, Y\rangle_F = \operatorname{Tr}(XY)$ and Frobenius norm $\|\cdot\|_2$, let $\mathcal L \subseteq \mathbf S^k$ be a linear subspace with orthogonal complement $\mathcal L^\perp$ in $\mathbf S^k$, and $B, C \in \mathbf S^k$. Consider the primal-dual pair
--
--   $$\text{(P)}\ \min_X\{\operatorname{Tr}(CX) : X \in (\mathcal L - B)\cap\mathbf S^k_+\},\qquad \text{(D)}\ \max_S\{\operatorname{Tr}(BS) : S \in (\mathcal L^\perp + C)\cap\mathbf S^k_+\}.$$
--
--   Let the parameters satisfy $0 < \chi \le \kappa \le 0.1$ (6.5.44), and let $\bar X \succ 0$, $\bar S \succ 0$ with $\bar X \in \mathcal L - B$, $\bar S \in \mathcal L^\perp + C$ (strictly feasible solutions of (P), (D)) be such that, with $\bar t = k/\operatorname{Tr}(\bar X\bar S)$ (6.5.38),
--
--   $$\|\bar t\,\bar X^{1/2}\bar S\bar X^{1/2} - I\|_2 \le \kappa \qquad (6.5.39).$$
--
--   The updating (U) sets $t_+ = (1 - \chi/\sqrt k)^{-1}\bar t$ (6.5.40), takes any $Q \succ 0$ such that $Q\bar XQ$ and $Q^{-1}\bar SQ^{-1}$ commute, and solves for symmetric $(\Delta X, \Delta S)$ the system $\Delta X \in \mathcal L$, $\Delta S \in \mathcal L^\perp$ (6.5.42),
--
--   $$Q[\Delta X\cdot\bar S + \bar X\cdot\Delta S]Q^{-1} + Q^{-1}[\Delta S\cdot\bar X + \bar S\cdot\Delta X]Q = \frac{2}{t_+}I - [Q\bar X\bar SQ^{-1} + Q^{-1}\bar S\bar XQ] \qquad (6.5.41),$$
--
--   then puts $X_+ = \bar X + \Delta X$, $S_+ = \bar S + \Delta S$. The theorem asserts, for every such $Q$:
--
--   1. the system (6.5.41), (6.5.42) has exactly one solution $(\Delta X, \Delta S)$;
--   2. $X_+$ and $S_+$ are strictly feasible solutions of (P) and (D);
--   3. $t_+ = k/\operatorname{Tr}(X_+S_+)$;
--   4. $(t_+, X_+, S_+) \in \mathcal N_\kappa$, that is, $t_+ > 0$ and $\|t_+X_+^{1/2}S_+X_+^{1/2} - I\|_2 \le \kappa$.
--
--   Iterating the step multiplies the penalty parameter by $(1-\chi/\sqrt k)^{-1}$ while staying close to the central path, which gives the $O(\sqrt k)$ steps per constant-factor reduction of the duality gap of short-step primal-dual methods for SDP.
--
--   **Formalization Note** Matrices are `Matrix (Fin k) (Fin k) ℝ`, $X^{1/2}$ is `CFC.sqrt`, and $\mathcal L$ is a submodule whose elements are symmetric. The book's (P) comes from a conic problem $\min\{c^Tx : \mathcal Ax - B \succeq 0\}$ under Assumption A ($\mathcal A$ injective) with $\mathcal L = \operatorname{Im}\mathcal A$; every subspace is such an image, so quantifying over subspaces is equivalent. The statement holds for every admissible scaling $Q$ (step 2 of (U) "chooses somehow" $Q$). Items 1 and 2–4 are stated as: a unique solution exists, and every solution has properties 2–4.
-- source:
--   Ben-Tal & Nemirovski, Lectures on Modern Convex Optimization, SIAM 2001, p. 412, Theorem 6.5.2 (with the updating (U), (6.5.38)–(6.5.42), pp. 411–412, and N_κ, (6.4.13), p. 396)

import Mathlib
import Definitions.Def_ModernConvex_PathFollowing_SDP

open Matrix
open scoped MatrixOrder

namespace ModernConvex.PathFollowing

/-- Ben-Tal–Nemirovski, Theorem 6.5.2, p. 412: let `0 < χ ≤ κ ≤ 0.1` (6.5.44) and let `(X̄, S̄)`
be strictly feasible solutions of `(P)`, `(D)` (with `K = Sᵏ₊`) such that, with
`t̄ = k/Tr(X̄S̄)` (6.5.38), `‖t̄X̄^{1/2}S̄X̄^{1/2} − I‖₂ ≤ κ` (6.5.39). Let `t₊ = (1 − χ/√k)⁻¹t̄`
(6.5.40) and let `Q ≻ 0` be any scaling matrix with `QX̄Q`, `Q⁻¹S̄Q⁻¹` commuting. Then the system
(6.5.41), (6.5.42) has a unique solution `(ΔX, ΔS)`, and `X₊ = X̄ + ΔX`, `S₊ = S̄ + ΔS` are
strictly feasible for `(P)`, `(D)`, `t₊ = k/Tr(X₊S₊)`, and `(t₊, X₊, S₊) ∈ N_κ`. -/
theorem primal_dual_update_step {k : ℕ} (hk : 0 < k) (P : SDPPair k) (κ χ : ℝ) (hχ : 0 < χ)
    (hχκ : χ ≤ κ) (hκ : κ ≤ 0.1) (X S : Matrix (Fin k) (Fin k) ℝ)
    (hX : P.StrictlyPrimalFeasible X) (hS : P.StrictlyDualFeasible S)
    (hclose : centralPathDist (penaltyOf X S) X S ≤ κ)
    (Q : Matrix (Fin k) (Fin k) ℝ) (hQ : IsCommutingScaling Q X S) :
    (∃! d : Matrix (Fin k) (Fin k) ℝ × Matrix (Fin k) (Fin k) ℝ,
        P.IsSearchDirection Q X S (nextPenalty k χ (penaltyOf X S)) d.1 d.2) ∧
      ∀ dX dS : Matrix (Fin k) (Fin k) ℝ,
        P.IsSearchDirection Q X S (nextPenalty k χ (penaltyOf X S)) dX dS →
          P.StrictlyPrimalFeasible (X + dX) ∧ P.StrictlyDualFeasible (S + dS) ∧
          nextPenalty k χ (penaltyOf X S) = penaltyOf (X + dX) (S + dS) ∧
          P.InNbhd κ (nextPenalty k χ (penaltyOf X S)) (X + dX) (S + dS) := by sorry

end ModernConvex.PathFollowing
