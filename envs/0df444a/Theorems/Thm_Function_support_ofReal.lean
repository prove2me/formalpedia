-- Prove2me | Theorems.Thm_Function_support_ofReal
-- name    : Function.support_ofReal
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-07-29T15:32:51.593746+00:00
-- url     : https://prove2.me/theorems/694eae92-9584-4390-ae06-dec99ec0a2a2
-- title:
--   Complexification does not change the support of a real function
-- statement:
--   Let $f : \mathbb{R} \to \mathbb{R}$. Then the support of the complexified function $x \mapsto (f(x) : \mathbb{C})$ coincides with the support of $f$:
--   $$\operatorname{supp}\bigl(x \mapsto (f(x):\mathbb{C})\bigr) = \operatorname{supp}(f).$$
--
--   This holds because the embedding $\mathbb{R} \hookrightarrow \mathbb{C}$ is injective and sends $0$ to $0$, so $f(x)$ vanishes as a complex number exactly when it vanishes as a real number.
--
--   In the PNT+ Mellin-calculus development, smoothing kernels $\nu$ are real functions with compact support in $[1/2, 2]$, but they enter complex contour integrals as complex-valued integrands; this lemma transports the support information (and hence integration-domain restrictions) across the complexification without any bookkeeping.
-- source:
--   https://github.com/AlexKontorovich/PrimeNumberTheoremAnd/blob/f55e85551ac10e96d98262a354cfcaac2825f2da/PrimeNumberTheoremAnd/MellinCalculus.lean#L96-L99

import Batteries.Tactic.Lemma
import Mathlib.Algebra.GroupWithZero.Units.Basic
import Mathlib.Analysis.MellinTransform
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.Tactic.Bound
import Mathlib.Tactic.GCongr
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.InnerProductSpace.Basic
import Definitions.Def_MellinCalculus_defs

open scoped ContDiff

set_option lang.lemmaCmd true

-- TODO: move near `MeasureTheory.setIntegral_prod`

-- How to deal with this coercion?... Ans: (f ·)
--- noncomputable def funCoe (f : ℝ → ℝ) : ℝ → ℂ := fun x ↦ f x

open Complex Topology Filter Real MeasureTheory Set

variable {𝕂 : Type*} [RCLike 𝕂]

-- TODO: generalize to `RCLike`

@[simp]

theorem Function.support_ofReal {f : ℝ → ℝ} :
    (fun x ↦ ((f x) : ℂ)).support = f.support := by sorry
