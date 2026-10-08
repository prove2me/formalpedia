-- Prove2me | Theorems.Thm_HryniewiczCriterion_positive_path_graph_angle_bound
-- name    : HryniewiczCriterion.positive_path_graph_angle_bound
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-06T15:23:00.367517+00:00
-- url     : https://prove2.me/theorems/fe83c257-af70-46a1-98bd-c14bbdedafd5
-- title:
--   Graph-angle bound for a positive symplectic path with two fixed directions
-- statement:
--   Let $\hat Y:\mathbb{R}\to\mathbb{R}^{4\times4}$ solve $\hat Y'=J\,S(t)\,\hat Y$, $\hat Y(0)=I$, where $S(t)$ is continuous and symmetric positive definite and $J$ is the standard complex structure in the coordinates $(q_1,p_1,q_2,p_2)$. Suppose that at some time $T>0$ the matrix $\hat Y(T)=\operatorname{diag}(I_2,g)$ fixes the first two coordinate directions.
--
--   For a symplectic matrix $M$ let $V(M)=W(\Gamma_M)\,W(\Delta)^{-1}$ be the graph unitary: $\Gamma_M=\{(z,Mz)\}$ is a Lagrangian in $(\mathbb{R}^4\oplus\mathbb{R}^4,-\omega_0\oplus\omega_0)$, $\Delta=\Gamma_I$, and $W(L)=UU^{\mathsf T}$ for a unitary basis $U$ of $L$. Let $\theta$ be a continuous determinant angle, $\det V(\hat Y(t))=e^{i\theta(t)}$ with $\theta(0)=0$. Then
--   $$\theta(T)\;\ge\;4\pi+\sum_{\lambda}\operatorname{ang}(\lambda),$$
--   where the sum runs over the eigenvalues $\lambda$ (with multiplicity) of the $2\times2$ graph unitary of $g$, and $\operatorname{ang}(\lambda)\in(0,2\pi]$ is the argument with $\operatorname{ang}(1)=2\pi$.
--
--   This is a finite-dimensional counterpart of HWZ (3.42)–(3.43): positivity of the generator, together with the two directions fixed at time $T$, forces the graph angle of the path to exceed the minimal value allowed by its endpoint by at least $4\pi$.
-- source:
--   Hofer–Wysocki–Zehnder, The dynamics on three-dimensional strictly convex energy surfaces, Ann. of Math. 148 (1998), https://doi.org/10.2307/120994, proof of Theorem 3.4, (3.42)–(3.43), p. 221–222, recast with the Souriau map $W(L)=UU^{\mathsf T}$ of the Lagrangian Grassmannian (Arnold; Robbin–Salamon, The Maslov index for paths, Topology 32 (1993)). Reduction lemma; not a verbatim numbered assertion.

import Definitions.Def_HryniewiczCriterion_GraphAngle

open HryniewiczCriterion
open scoped ContDiff

theorem HryniewiczCriterion.positive_path_graph_angle_bound (Ŷ S : ℝ → Matrix (Fin 4) (Fin 4) ℝ) (T : ℝ)
    (hT : 0 < T) (hSc : ∀ i j : Fin 4, Continuous fun t => S t i j) (hSpos : ∀ t, (S t).PosDef)
    (h0 : Ŷ 0 = 1)
    (hd : ∀ t : ℝ, ∀ i j : Fin 4, HasDerivAt (fun s => Ŷ s i j) ((symplJ4 * S t * Ŷ t) i j) t)
    (g : Matrix (Fin 2) (Fin 2) ℝ) (hend : Ŷ T = blockOne g) (θ : ℝ → ℝ)
    (hθ : IsDetAngleLift (fun t => graphUnitary4 (Ŷ t)) T θ) :
    4 * Real.pi + eigenAngleSum (graphUnitary2 g) ≤ θ T := by sorry
