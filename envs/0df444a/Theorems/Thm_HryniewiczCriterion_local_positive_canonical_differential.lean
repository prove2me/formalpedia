-- Prove2me | Theorems.Thm_HryniewiczCriterion_local_positive_canonical_differential
-- name    : HryniewiczCriterion.local_positive_canonical_differential
-- status  : Proved
-- author  : @Johan Mercedes
-- created : 2026-10-29T17:47:33.050415+00:00
-- url     : https://prove2.me/theorems/a37ec978-41a3-400f-adc7-cc9064563d3e
-- title:
--   Positive canonical differential system from a tangentially convex orbit
-- statement:
--   Let $H:\mathbb R^4\to\mathbb R$ be $C^2$ at every point of a Hamiltonian solution $x(t)$. Suppose $r(t)=dH(x(t))x(t)>0$ and $D^2H(x(t))$ is positive on every nonzero vector in $\ker dH(x(t))$. Let $Y$ be the variational flow with $Y(0)=I$, and let $F(t)$ be the radial contact frame, assumed symplectic. For any nonzero time scale $T$, define the transverse block
--
--   $$\varphi(\tau)=\left[F(\tau T)^{-1}Y(\tau T)F(0)\right]_{\{2,3\}\times\{2,3\}}.$$
--
--   Then $\det\varphi(\tau)=1$ for every $\tau$. Moreover, there is a continuous symmetric positive definite matrix $S(t)$ such that
--
--   $$Z(t)=F(0)^{-1}F(t)\operatorname{diag}(I_2,\varphi(t/T)),\qquad \dot Z(t)=JS(t)Z(t).$$
--
--   This supplies the local positive-system part of the canonical orbit model. Neither global homogeneity of $H$ nor periodicity of the orbit is required for this differential statement; periodicity is imposed separately when applying the winding estimate.
-- source:
--   Derived local completion and frame-flow argument for https://prove2.me/theorems/55100510-e824-4da4-8931-8673d294fb84. Positive radial Hessian completion: https://prove2.me/theorems/7467caf1-ef17-48cf-bbaa-0c7d3dd9dea8. Generic jvec, symplectic-pairing, Hessian-matrix and conjugation calculations adapted with credit to Mazecto’s accepted homogeneous_frame_flow_split / homogeneous_graph_angle_transport sources, including submission893234ef-5ec2-4f4b-b415-f79ec1030002, https://prove2.me/theorems/f880a9bf-1521-4b02-a828-1c90ceda0bb1. Context: HWZ Ann.Math.148(1998), equations(3.33)-(3.39), https://doi.org/10.2307/120994. The C2 local completion theorem is derived here, not a verbatim numbered source statement.

import Definitions.Def_BirkhoffGlobalSection_MovingFrameAlgebra
open HryniewiczCriterion
open scoped ContDiff

theorem HryniewiczCriterion.local_positive_canonical_differential
    (H : R4 → ℝ) (x : ℝ → R4) (T : ℝ) (hT : T ≠ 0)
    (hH : ∀ t, ContDiffAt ℝ 2 H (x t))
    (hx : ∀ t, HasDerivAt x (HryniewiczCriterion.hamiltonianVectorField H (x t)) t)
    (hr : ∀ t, 0 < fderiv ℝ H (x t) (x t))
    (hB : ∀ t v, fderiv ℝ H (x t) v = 0 → v ≠ 0 →
      0 < fderiv ℝ (fderiv ℝ H) (x t) v v)
    (Y : ℝ → (R4 →L[ℝ] R4)) (hY : IsLinearizedFlow H x Y)
    (hFsp : ∀ t, (homogFrame H (x t)).transpose * omegaMat * homogFrame H (x t) = omegaMat) :
    let F := fun t => homogFrame H (x t)
    let φ : ℝ → Matrix (Fin 2) (Fin 2) ℝ := fun τ i j =>
      ((F (τ * T))⁻¹ * LinearMap.toMatrix' (Y (τ * T) : R4 →ₗ[ℝ] R4) * F 0)
        i.succ.succ j.succ.succ
    (∀ τ, (φ τ).det = 1) ∧
    (∃ S : ℝ → Matrix (Fin 4) (Fin 4) ℝ,
      (∀ i j, Continuous fun t => S t i j) ∧ (∀ t, (S t).PosDef) ∧
      ∀ t i j, HasDerivAt (fun s => ((F 0)⁻¹ * F s * blockOne (φ (s / T))) i j)
        ((symplJ4 * S t * ((F 0)⁻¹ * F t * blockOne (φ (t / T)))) i j) t) := by sorry
