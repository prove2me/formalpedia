-- Prove2me | Theorems.Thm_OAI_PermanentBorder_PolarAnalysis_simple_polarPair_unit
-- name    : OAI.PermanentBorder.PolarAnalysis.simple_polarPair_unit
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T22:43:08.496557+00:00
-- url     : https://prove2.me/theorems/0d528b23-cf63-4e31-adce-0ead1e08f5e3
-- title:
--   Simple zeros of a polar system survive removal of a nonvanishing factor
-- statement:
--   Let $T$ and $V$ be complex normed spaces, $\kappa$ a finite set, $\psi:V\to T$ a map, $h=(h_k)_{k\in\kappa}$ a family of directions in $T$, and $x\in V$. For a function $G:T\to\mathbb{C}$ define its *polar map*
--   $$\mathcal P_G:V\to\mathbb{C}\times\mathbb{C}^{\kappa},\qquad\mathcal P_G(y)=\Big(G(\psi(y)),\ \big(DG(\psi(y))[h_k]\big)_{k\in\kappa}\Big),$$
--   the value of $G$ at $\psi(y)$ together with its directional derivatives in the directions $h_k$. Let $F,c,S:T\to\mathbb{C}$ and assume:
--
--   1. $c$ and $S$ are twice continuously complex differentiable at $\psi(x)$, and $\psi$ is complex differentiable at $x$;
--   2. $F=c\,S$ on a neighbourhood of $\psi(x)$, and $c(\psi(x))\neq0$;
--   3. $x$ is a simple zero of $\mathcal P_F$: $\mathcal P_F(x)=0$ and the derivative $D\mathcal P_F(x):V\to\mathbb{C}\times\mathbb{C}^{\kappa}$ is invertible.
--
--   Then $x$ is a simple zero of $\mathcal P_S$:
--
--   $$
--   \mathcal P_S(x)=0\qquad\text{and}\qquad D\mathcal P_S(x)\ \text{ is invertible}.
--   $$
--
--   Typical instances are $F=\det M$ for a matrix family $M$ with $c=\det E$ for an invertible block $E$ and $S$ the corresponding Schur complement, or $c$ a nonzero constant. The result shows that simple zeros of the polar system of $F$ are simple zeros of the polar system of the factor $S$, so they can be studied through $S$.
--
--   **Formalization Note** $\mathcal P_G$ is `polarPair G ψ h`; invertibility is `ContinuousLinearMap.IsInvertible` of `fderiv ℂ`, i.e. the derivative is a continuous linear equivalence between $V$ and $\mathbb{C}\times\mathbb{C}^{\kappa}$; twice continuous differentiability at a point is `ContDiffAt ℂ 2`; the factorisation $F=cS$ is an eventual equality in the neighbourhood filter of $\psi(x)$. No differentiability of $F$ is assumed separately.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Algebra/Determinantal/SchurDifferentials.lean#L376-L409

import Mathlib
import Definitions.Def_SmoothInitialForm
import Definitions.Def_OAI_Algebra_Determinantal_Multigraded
import Definitions.Def_OAI_Algebra_Determinantal_LinearForms
import Definitions.Def_OAI_Algebra_Determinantal_PointBounds
import Definitions.Def_OAI_Algebra_Determinantal_ProjectiveCounts
import Definitions.Def_OAI_Algebra_Determinantal_KernelCharts
import Definitions.Def_OAI_Algebra_Determinantal_SchurDifferentials

open OAI OAI.PermanentBorder OAI.PermanentBorder.PolarAnalysis
open Filter
open scoped Topology
variable {T V : Type*} [NormedAddCommGroup T] [NormedSpace ℂ T]
  [NormedAddCommGroup V] [NormedSpace ℂ V]
variable {κ : Type*} [Fintype κ]

theorem OAI.PermanentBorder.PolarAnalysis.simple_polarPair_unit {F c S : T → ℂ} {ψ : V → T} {h : κ → T} {x : V}
    (hc : ContDiffAt ℂ 2 c (ψ x)) (hS : ContDiffAt ℂ 2 S (ψ x))
    (hψ : DifferentiableAt ℂ ψ x)
    (hFS : F =ᶠ[𝓝 (ψ x)] (fun y => c y * S y)) (hcx : c (ψ x) ≠ 0)
    (hz : polarPair F ψ h x = 0)
    (hsimple : (fderiv ℂ (polarPair F ψ h) x).IsInvertible) :
    polarPair S ψ h x = 0 ∧ (fderiv ℂ (polarPair S ψ h) x).IsInvertible := by sorry
