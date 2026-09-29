-- Prove2me | Theorems.Thm_ModularForm_mdifferentiable_heckeT
-- name    : ModularForm.mdifferentiable_heckeT
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:55.335791+00:00
-- url     : https://prove2.me/theorems/2743fa4f-4160-5456-aeb8-0f6485a20067
-- title:
--   Holomorphy of Tₚ f for holomorphic f
-- statement:
--   Let $f : \mathbb{H} \to \mathbb{C}$ be a function on the upper half-plane which is `MDifferentiable` for the standard self-model-with-corners of $\mathbb{C}$ on both source and target, i.e. holomorphic as a map between the complex manifolds $\mathbb{H}$ and $\mathbb{C}$. Let $k$ be an integer and $p$ a natural number. Then the function [`ModularForm.heckeT k p f`](def/ModularForm_HeckeOperator.html#L96), defined as the sum $\sum_{j \in \{0,\dots,p-1\}} f \mid[k] \,$`heckeMatrix p j` $+\; f \mid[k] \,$`heckeDiagMatrix p`, is again holomorphic in the same sense, where $\mid[k]$ is the weight-$k$ slash action of $\mathrm{GL}_2(\mathbb{R})$ on functions on $\mathbb{H}$, the matrices `heckeMatrix p j` are the $p$ upper-triangular representatives used in the project's definition of `heckeU`, and `heckeDiagMatrix p` is the identity when $p = 0$ and the element `upperTriangularGL p 0 1` of $\mathrm{GL}_2(\mathbb{R})$ otherwise. No positivity, primality or non-vanishing assumption is imposed on $p$; for $p = 0$ the first sum is empty and the statement reduces to the holomorphy of $f \mid[k] 1$.
--
--   This is the holomorphy half of the standard statement that the Hecke operator $T_p$ preserves holomorphic functions on $\mathbb{H}$, formulated for arbitrary functions rather than only for modular or cusp forms. It is used when assembling $T_p$ on spaces of cusp forms, for instance in the results producing a cusp form whose underlying function is `heckeT k p f` and in the computations of $q$-expansion coefficients of $T_p$-eigenforms.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularForm_mdifferentiable_heckeT.lean

import Mathlib
import Definitions.Def_ModularForm_HeckeOperator
import Definitions.Def_FLTPrelim_Modularity

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem ModularForm.mdifferentiable_heckeT {f : UpperHalfPlane → ℂ} (hf : MDifferentiable (modelWithCornersSelf ℂ ℂ) (modelWithCornersSelf ℂ ℂ) f) (k : ℤ) (p : ℕ) : MDifferentiable (modelWithCornersSelf ℂ ℂ) (modelWithCornersSelf ℂ ℂ) (ModularForm.heckeT k p f) := by sorry
