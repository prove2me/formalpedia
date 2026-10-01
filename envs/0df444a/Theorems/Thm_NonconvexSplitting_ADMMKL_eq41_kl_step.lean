-- Prove2me | Theorems.Thm_NonconvexSplitting_ADMMKL_eq41_kl_step
-- name    : NonconvexSplitting.ADMMKL.eq41_kl_step
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-29T18:35:21.928422+00:00
-- url     : https://prove2.me/theorems/c146921c-a484-4411-8f93-5b979d66288c
-- title:
--   Eq. (41) — the one-step KL estimate
-- statement:
--   Let $h$, $P$, $\mathcal M$, $\beta$ and $L_\beta$ be as in the paper, regarded on $\mathcal X=\mathbb R^n\times\mathbb R^m\times\mathbb R^m$, and let $(x^t,y^t,z^t)_{t\ge0}$ be any sequences. Assume:
--
--   1. constants $C,D>0$ with, for all $t\ge1$, some $w\in\partial L_\beta(x^{t+1},y^{t+1},z^{t+1})$ with $\|w\|\le C\|x^{t+1}-x^t\|$ (the conclusion of (35)), and $L_\beta(x^t,y^t,z^t)-L_\beta(x^{t+1},y^{t+1},z^{t+1})\ge D\|x^{t+1}-x^t\|^2$ (the conclusion of (36));
--   2. a real $l^*$ with $L_\beta(x^t,y^t,z^t)>l^*$ for all $t\ge1$;
--   3. $\eta>0$, a set $V\subseteq\mathcal X$ and $\varphi$ satisfying condition (i) of Definition 1 on $[0,\eta)$, such that the KL inequality (40) holds: for all $(x,y,z)\in V$ with $l^*<L_\beta(x,y,z)<l^*+\eta$ and all $v\in\partial L_\beta(x,y,z)$, $\varphi'(L_\beta(x,y,z)-l^*)\,\|v\|\ge1$.
--
--   Then for every $t\ge2$ with $(x^t,y^t,z^t)\in V$ and $l^*<L_\beta(x^t,y^t,z^t)<l^*+\eta$,
--   $$
--   \|x^{t+1}-x^t\|+\bigl(\|x^{t+1}-x^t\|-\|x^t-x^{t-1}\|\bigr)\le\frac CD\Bigl[\varphi\bigl(L_\beta(x^t,y^t,z^t)-l^*\bigr)-\varphi\bigl(L_\beta(x^{t+1},y^{t+1},z^{t+1})-l^*\bigr)\Bigr].
--   $$
--
--   Summing this inequality telescopes the right-hand side and yields the finite length (34).
--
--   **Formalization Note** The paper states (41) for the ADMM sequence under "$x^t\in B_\rho$ and $t\ge N_0$", which it uses only to conclude $(x^t,y^t,z^t)\in\mathbf B_\rho\subseteq V$; this statement assumes $(x^t,y^t,z^t)\in V$ directly and takes (35), (36) and the case assumption $L_\beta>l^*$ as hypotheses, so it is implied by the paper's version. The range $t\ge2$ comes from applying (35) at index $t-1\ge1$. Values of $L_\beta$ are in `EReal`; under the stated bounds the differences $L_\beta-l^*$ are finite reals and are converted with `toReal`.
-- source:
--   Li & Pong, Global Convergence of Splitting Methods for Nonconvex Composite Optimization, arXiv:1407.0753v6, p. 15, Eq. (41) and the display after it

import Mathlib
import Definitions.Def_NonconvexSplitting_Shared_IsProxADMMSeq
import Definitions.Def_NonconvexSplitting_Shared_LimitingSubdiff
import Definitions.Def_NonconvexSplitting_ADMMKL_AugLagProd
import Definitions.Def_NonconvexSplitting_ADMMKL_KLProperty
open NonconvexSplitting.Shared

open Filter Topology
open scoped InnerProductSpace

namespace NonconvexSplitting.ADMMKL

/-- Eq. (41) of Li–Pong (p. 15), in self-contained form. Let `(x^t, y^t, z^t)` be sequences and
`C, D > 0` constants satisfying the conclusions of (35) and (36) for `t ≥ 1`, let `l*` be a real
number with `L_β(x^t, y^t, z^t) > l*` for all `t ≥ 1`, and let `η > 0`, `V` and `φ` satisfy
condition (i) of Definition 1 and the KL inequality (40) at level `l*` on `V`. Then for every
`t ≥ 2` with `(x^t, y^t, z^t) ∈ V` and `l* < L_β(x^t, y^t, z^t) < l* + η`,
`‖x^{t+1} - x^t‖ + (‖x^{t+1} - x^t‖ - ‖x^t - x^{t-1}‖)
  ≤ (C/D) [φ(L_β(x^t, y^t, z^t) - l*) - φ(L_β(x^{t+1}, y^{t+1}, z^{t+1}) - l*)]`. -/
theorem eq41_kl_step {n m : ℕ} (h : EuclideanSpace ℝ (Fin n) → ℝ) (P : EuclideanSpace ℝ (Fin m) → EReal)
    (M : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin m)) (β : ℝ)
    (x : ℕ → EuclideanSpace ℝ (Fin n)) (y z : ℕ → EuclideanSpace ℝ (Fin m))
    (C D : ℝ) (hC : 0 < C) (hD : 0 < D)
    (h35 : ∀ t : ℕ, 1 ≤ t →
      ∃ w ∈ LimitingSubdiff (augLagX h P M β) (pack (x (t + 1)) (y (t + 1)) (z (t + 1))),
        ‖w‖ ≤ C * ‖x (t + 1) - x t‖)
    (h36 : ∀ t : ℕ, 1 ≤ t →
      augLag h P M β (x (t + 1)) (y (t + 1)) (z (t + 1)) + ((D * ‖x (t + 1) - x t‖ ^ 2 : ℝ) : EReal) ≤
        augLag h P M β (x t) (y t) (z t))
    (lstar : ℝ) (hgt : ∀ t : ℕ, 1 ≤ t → (lstar : EReal) < augLag h P M β (x t) (y t) (z t))
    (η : ℝ) (hη : 0 < η) (V : Set (XYZ n m)) (φ : ℝ → ℝ) (hφ : IsDesingularizer η φ)
    (h40 : ∀ w ∈ V, (lstar : EReal) < augLagX h P M β w →
      augLagX h P M β w < (lstar : EReal) + (η : EReal) →
      ∀ v ∈ LimitingSubdiff (augLagX h P M β) w,
        1 ≤ deriv φ (augLagX h P M β w - (lstar : EReal)).toReal * ‖v‖)
    (t : ℕ) (ht : 2 ≤ t) (hV : pack (x t) (y t) (z t) ∈ V)
    (hlo : (lstar : EReal) < augLag h P M β (x t) (y t) (z t))
    (hhi : augLag h P M β (x t) (y t) (z t) < (lstar : EReal) + (η : EReal)) :
    ‖x (t + 1) - x t‖ + (‖x (t + 1) - x t‖ - ‖x t - x (t - 1)‖) ≤
      C / D * (φ (augLag h P M β (x t) (y t) (z t) - (lstar : EReal)).toReal -
        φ (augLag h P M β (x (t + 1)) (y (t + 1)) (z (t + 1)) - (lstar : EReal)).toReal) := by sorry

end NonconvexSplitting.ADMMKL
