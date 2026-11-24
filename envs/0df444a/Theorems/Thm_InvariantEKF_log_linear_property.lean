-- Prove2me | Theorems.Thm_InvariantEKF_log_linear_property
-- name    : InvariantEKF.log_linear_property
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-24T01:18:29.653904+00:00
-- url     : https://prove2.me/theorems/d07accb7-d546-44e0-9bfe-657e4101e851
-- title:
--   Theorem 2: log-linear property of the invariant error
-- statement:
--   Let $G$ be a matrix Lie group with Lie algebra coordinates $\mathcal L_{\mathfrak g}$ and exponential $\exp(\xi)=\exp_m(\mathcal L_{\mathfrak g}(\xi))$. Let the system $\frac{d}{dt}\chi_t=f_{u_t}(\chi_t)$ be group affine (eq. 12). Assume it is locally Lipschitz in the state, uniformly on compact time windows, and forward complete on $G$. Let $\eta^i_t$ ($i=L$ or $R$) be the invariant error between two trajectories $\chi,\bar\chi$ on $[0,\infty)$. Let $A^i_{u_t}$ be defined by $g^i_{u_t}(\exp\xi)=\mathcal L_{\mathfrak g}(A^i_{u_t}\xi)+O(\|\xi\|^2)$. Take $\xi^i_0$ with $\exp(\xi^i_0)=\eta^i_0$, and let $\xi^i_t$ solve the linear equation
--
--   $$\frac{d}{dt}\xi^i_t=A^i_{u_t}\xi^i_t\quad(t>0),$$
--
--   continuously at $t=0$. Then, for arbitrarily large errors,
--
--   $$\eta^i_t=\exp(\xi^i_t)\qquad\text{for all }t\ge0 .$$
--
--   **Formalization Note** Local Lipschitz continuity and forward completeness are standing assumptions behind "the flow" used in the paper's proof (Appendix B). They are kept as in the paper; forward completeness is not needed for the truth of the statement. The $O(\|\xi\|^2)$ is stated with explicit constants for each $t$.
-- source:
--   Barrau and Bonnabel, The invariant extended Kalman filter as a stable observer, arXiv:1410.1465v4 (2015), Section 2.3, Theorem 2, eqs. (12)-(13), p. 7; proof in Appendix B, Theorem 7, p. 26

import Mathlib
import Definitions.Def_InvariantEKF_Basic

open MeasureTheory Matrix Filter Topology

namespace InvariantEKF

theorem log_linear_property {N d : ℕ} {U : Type*} (left : Bool)
    (G : Set (Matrix (Fin N) (Fin N) ℝ)) (hG : IsMatrixLieGroup G)
    (L : (Fin d → ℝ) →ₗ[ℝ] Matrix (Fin N) (Fin N) ℝ) (hL : IsLieAlgebraCoords G L)
    (f : U → Matrix (Fin N) (Fin N) ℝ → Matrix (Fin N) (Fin N) ℝ) (hf : IsGroupAffine G f)
    (u : ℝ → U) (hreg : IsLocLipschitzField (fun t => f (u t)))
    (hcomplete : ∀ a ∈ G, ∃ χ, IsTrajectory G f u (Set.Ici 0) χ ∧ χ 0 = a)
    (A : U → Matrix (Fin d) (Fin d) ℝ)
    (hA : ∀ t, 0 ≤ t → IsLinearization L (errField left f (u t)) (A (u t)))
    (χ χbar : ℝ → Matrix (Fin N) (Fin N) ℝ)
    (hχ : IsTrajectory G f u (Set.Ici 0) χ) (hχbar : IsTrajectory G f u (Set.Ici 0) χbar)
    (ξ : ℝ → Fin d → ℝ) (hξ0 : expG L (ξ 0) = invError left (χ 0) (χbar 0))
    (hξc : ContinuousWithinAt ξ (Set.Ici 0) 0)
    (hξ : ∀ t, 0 < t → HasDerivAt ξ (A (u t) *ᵥ ξ t) t) :
    ∀ t, 0 ≤ t → invError left (χ t) (χbar t) = expG L (ξ t) := by sorry

end InvariantEKF
