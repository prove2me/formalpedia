-- Prove2me | Theorems.Thm_InvariantEKF_error_autonomy_iff
-- name    : InvariantEKF.error_autonomy_iff
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-24T01:16:49.815632+00:00
-- url     : https://prove2.me/theorems/414610d0-abba-491b-b752-a0f6389a46a2
-- title:
--   Theorem 1: the invariant errors are state-trajectory independent iff $f_u(ab)=f_u(a)b+af_u(b)-af_u(I_d)b$
-- statement:
--   Let $G$ be a matrix Lie group and consider the system $\frac{d}{dt}\chi_t=f_{u_t}(\chi_t)$ on $G$, for $t>0$. Assume that for every $t>0$ and $a\in G$ some trajectory passes through $a$ at time $t$. Then the following are equivalent:
--
--   1. the left-invariant error $\eta^L_t=\chi_t^{-1}\bar\chi_t$ is state-trajectory independent;
--   2. the right-invariant error $\eta^R_t=\bar\chi_t\chi_t^{-1}$ is state-trajectory independent;
--   3. for all $t>0$ and $a,b\in G$,
--   $$f_{u_t}(ab)=f_{u_t}(a)\,b+a\,f_{u_t}(b)-a\,f_{u_t}(I)\,b .$$
--
--   Moreover, under 3, for any two trajectories and every $t>0$,
--   $$\frac{d}{dt}\eta^L_t=f_{u_t}(\eta^L_t)-f_{u_t}(I)\eta^L_t,\qquad \frac{d}{dt}\eta^R_t=f_{u_t}(\eta^R_t)-\eta^R_tf_{u_t}(I).$$
--
--   **Formalization Note** "State-trajectory independent" (Definition 1) means that a single function $g$ gives $\frac{d}{dt}\eta_t=g_{u_t}(\eta_t)$ for every pair of trajectories. The paper does not state the existence of trajectories through every point, but its proof uses it ("this has to hold for any $\chi_t$ and $\eta^L_t$"). Without it, conditions 1 and 2 can hold vacuously.
-- source:
--   Barrau and Bonnabel, The invariant extended Kalman filter as a stable observer, arXiv:1410.1465v4 (2015), Section 2.2, Definition 1 and Theorem 1, eqs. (4)-(9), pp. 5-6

import Mathlib
import Definitions.Def_InvariantEKF_Basic

open MeasureTheory Matrix Filter Topology

namespace InvariantEKF

theorem error_autonomy_iff {N : ℕ} {U : Type*} (G : Set (Matrix (Fin N) (Fin N) ℝ))
    (hG : IsMatrixLieGroup G) (f : U → Matrix (Fin N) (Fin N) ℝ → Matrix (Fin N) (Fin N) ℝ)
    (u : ℝ → U)
    (hexist : ∀ t, 0 < t → ∀ a ∈ G, ∃ χ, IsTrajectory G f u (Set.Ioi 0) χ ∧ χ t = a) :
    (ErrorAutonomous true G f u ↔ ErrorAutonomous false G f u) ∧
    (ErrorAutonomous false G f u ↔
      ∀ t, 0 < t → ∀ a ∈ G, ∀ b ∈ G,
        f (u t) (a * b) = f (u t) a * b + a * f (u t) b - a * f (u t) 1 * b) ∧
    ((∀ t, 0 < t → ∀ a ∈ G, ∀ b ∈ G,
        f (u t) (a * b) = f (u t) a * b + a * f (u t) b - a * f (u t) 1 * b) →
      ∀ χ χbar : ℝ → Matrix (Fin N) (Fin N) ℝ,
        IsTrajectory G f u (Set.Ioi 0) χ → IsTrajectory G f u (Set.Ioi 0) χbar →
        ∀ t, 0 < t →
          HasMatDerivAt (fun s => invError true (χ s) (χbar s))
            (errField true f (u t) (invError true (χ t) (χbar t))) t ∧
          HasMatDerivAt (fun s => invError false (χ s) (χbar s))
            (errField false f (u t) (invError false (χ t) (χbar t))) t) := by sorry

end InvariantEKF
