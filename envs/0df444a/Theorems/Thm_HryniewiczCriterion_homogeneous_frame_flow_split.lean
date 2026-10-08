-- Prove2me | Theorems.Thm_HryniewiczCriterion_homogeneous_frame_flow_split
-- name    : HryniewiczCriterion.homogeneous_frame_flow_split
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-06T15:22:48.682033+00:00
-- url     : https://prove2.me/theorems/6eddbaa1-2e75-45c3-8798-b233d355f366
-- title:
--   Invariant splitting of the linearized flow of a homogeneous convex model
-- statement:
--   Let $K$ be a homogeneous convex model, $Q=(x,T)$ a periodic orbit of $X_K$ on $S=K^{-1}(1)$ and $Z$ its normalized variational flow. Let $F$ be the symplectic frame of $\mathbb{R}^4$ at $x(0)$ with columns $x(0)$, $X_K(x(0))/\omega_0(x(0),X_K(x(0)))$, $Z_1(x(0))$, $Z_2(x(0))$, and put $\hat Y(t)=F^{-1}Z(t)F$. Then:
--
--   1. the contact-plane path $\varphi$ of $(K,Q,Z)$ is a smooth path in $SL(2,\mathbb{R})$ on $[0,1]$ with $\varphi(0)=I$;
--   2. $\hat Y(0)=I$, and $\hat Y'(t)=J\,S(t)\,\hat Y(t)$ for all $t$, where $J$ is the matrix with $X_H=J\nabla H$ and $S(t)$ is continuous and symmetric positive definite (namely $S(t)=F^{\mathsf T}D^2K(x(t))F$);
--   3. after one period, $\hat Y(T)=\operatorname{diag}(I_2,\varphi(1))$.
--
--   Item 3 is the invariant splitting $\mathbb{R}^4=\operatorname{span}\{x,X_K(x)\}\oplus\xi_x$ of HWZ (3.34)–(3.36): by homogeneity the linearized flow maps $x(0)$ to $x(t)$ and $X_K(x(0))$ to $X_K(x(t))$, and it preserves $\xi$.
-- source:
--   Hofer–Wysocki–Zehnder, The dynamics on three-dimensional strictly convex energy surfaces, Ann. of Math. 148 (1998), https://doi.org/10.2307/120994, Section 3, (3.33)–(3.39), pp. 220–221, with the global frame and contact path of Hryniewicz, https://arxiv.org/html/1105.2077v5, Section 2.1.1, equations (4)–(5) (frame $Z_1,Z_2$ of Hryniewicz §3, p. 12).

import Definitions.Def_HryniewiczCriterion_GraphAngle

open HryniewiczCriterion
open scoped ContDiff

theorem HryniewiczCriterion.homogeneous_frame_flow_split (K : R4 → ℝ) (hK : IsHomogeneousConvexModel K)
    (Q : PeriodicOrbit K) (Z : ℝ → (R4 →L[ℝ] R4)) (hZ : IsLinearizedFlow K Q.x Z) :
    (ContDiffOn ℝ ∞ (fun t i j => linearizedXiPath K Q Z t i j) (Set.Icc 0 1) ∧
      (∀ t ∈ Set.Icc (0 : ℝ) 1, (linearizedXiPath K Q Z t).det = 1) ∧
      linearizedXiPath K Q Z 0 = 1) ∧
    frameFlowMatrix K Q Z 0 = 1 ∧
    (∃ S : ℝ → Matrix (Fin 4) (Fin 4) ℝ, (∀ i j : Fin 4, Continuous fun t => S t i j) ∧
      (∀ t, (S t).PosDef) ∧
      ∀ t : ℝ, ∀ i j : Fin 4, HasDerivAt (fun s => frameFlowMatrix K Q Z s i j)
        ((symplJ4 * S t * frameFlowMatrix K Q Z t) i j) t) ∧
    frameFlowMatrix K Q Z Q.T = blockOne (linearizedXiPath K Q Z 1) := by sorry
