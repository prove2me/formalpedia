-- Prove2me | Theorems.Thm_KerrBL_vacuum_Kerr
-- name    : KerrBL.vacuum_Kerr
-- status  : Proved
-- author  : @He Wang
-- created : 2026-09-09T09:37:00.441657+00:00
-- url     : https://prove2.me/theorems/02986adc-5e4a-4617-9c1d-a7324a32b1af
-- title:
--   Kerr vacuum theorem in Boyer-Lindquist coordinates (headline)
-- statement:
--   Let $M,a\in\mathbb R$ and let $x=(t,r,\theta,\varphi)\in\mathbb R^4$ lie in the regular coordinate domain
--
--   $$\Sigma=r^2+a^2\cos^2\theta\neq0,\qquad \Delta=r^2-2Mr+a^2\neq0,\qquad \sin\theta\neq0 .$$
--
--   Let $g$ be the Boyer-Lindquist Kerr metric and $\hat g$ its closed-form inverse (`KerrBL_Kerr_Metric`), and let $\Gamma$ and $R$ be the generic coordinate Christoffel symbols and Ricci tensor of the specification layer (`KerrBL_CoordGeometry`), built from $g$, $\hat g$ and Mathlib's slice derivatives. Then all of the following hold:
--
--   1. $\hat g$ is a left inverse of $g$ at $x$: $\sum_k\hat g^{ik}(x)g_{kj}(x)=\delta_{ij}$ for all $i,j$;
--   2. for all $l,i,j$ the slice $u\mapsto g_{ij}(x[l\mapsto u])$ is differentiable at $u=x_l$;
--   3. for all $l,i,j,k$ the slice $u\mapsto\Gamma^i_{jk}(x[l\mapsto u])$ is differentiable at $u=x_l$;
--   4. the coordinate Ricci tensor vanishes:
--   $$R_{bd}(x)=0\qquad\text{for all } b,d\in\{0,1,2,3\}.$$
--
--   This is the goal theorem of the mission: a machine-checked coordinate verification that the Boyer-Lindquist Kerr family is Ricci-flat on the regular coordinate domain used by the formalization, for arbitrary real $M,a$. Clauses 1-3 make the statement self-contained: they exclude a trivialising inverse and exclude Mathlib's junk value for non-differentiable slices, so that clause 4 is a statement about the genuine coordinate Ricci tensor. The theorem does not assert a Lorentzian manifold, a global chart, the signature, positivity of $M$, the black-hole bound $|a|\le M$, anything on the axis $\sin\theta=0$ or at $\Sigma=0$, $\Delta=0$, or any coordinate-independent curvature statement.
--
--   **Formalization Note** The trusted base is the 45-line generic layer and the metric transcription (source-locked to the project certificate); every closed form is bridged by proof. The theorem depends only on the axioms `propext`, `Classical.choice`, `Quot.sound`.
-- source:
--   R. P. Kerr, Gravitational field of a spinning mass as an example of algebraically special metrics, Phys. Rev. Lett. 11 (1963) 237-238, https://doi.org/10.1103/PhysRevLett.11.237; R. H. Boyer and R. W. Lindquist, Maximal analytic extension of the Kerr metric, J. Math. Phys. 8 (1967) 265-281, https://doi.org/10.1063/1.1705193, Sec. 2 (Boyer-Lindquist form of the Kerr line element); metric components transcribed token-for-token from the project certificate EinsteinSolver/certificate/kerr/metric.json (sha256 d729883d95fd7d3cf84d9c971c6725f847155562cc4e88660535b8d0bd0be336); design record LEAN/kerr-formalization/mission/DESIGN.md, node N23 (vacuum_Kerr, goal)

import Definitions.Def_KerrBL_Kerr_Metric
open KerrBL Filter Topology

theorem KerrBL.vacuum_Kerr (M a : ℝ) (x : Pt) (hx : RegKerr M a x) :
    (∀ i j : Fin 4, (∑ k : Fin 4, giKerr M a i k x * gKerr M a k j x) = (if i = j then 1 else 0)) ∧
    (∀ l i j : Fin 4, DifferentiableAt ℝ (fun u => gKerr M a i j (Function.update x l u)) (x l)) ∧
    (∀ l i j k : Fin 4, DifferentiableAt ℝ (fun u => christoffel (gKerr M a) (giKerr M a) i j k (Function.update x l u)) (x l)) ∧
    (∀ b d : Fin 4, ricciOf (gKerr M a) (giKerr M a) b d x = 0) := by sorry
