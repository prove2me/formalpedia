-- Prove2me | Theorems.Thm_MellinOfDeltaSpike
-- name    : MellinOfDeltaSpike
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-07-29T15:34:38.40003+00:00
-- url     : https://prove2.me/theorems/3fb4d986-fcbb-4fc3-ba57-7843cf54efd8
-- title:
--   Mellin transform of the delta spike: $\mathcal{M}(\nu_\varepsilon)(s)=\mathcal{M}\nu(\varepsilon s)$
-- statement:
--   Let $\nu\colon\mathbb{R}\to\mathbb{R}$ be any function, let $\varepsilon>0$, and let $s\in\mathbb{C}$. Define the delta spike (multiplicative rescaling of $\nu$ toward the point $x=1$) by
--
--   $$\nu_\varepsilon(x) \;=\; \frac{1}{\varepsilon}\,\nu\!\left(x^{1/\varepsilon}\right).$$
--
--   Then the Mellin transform of the delta spike is a dilation of the Mellin transform of $\nu$:
--
--   $$\mathcal{M}(\nu_\varepsilon)(s) \;=\; \mathcal{M}\nu(\varepsilon s).$$
--
--   The rescaling $x\mapsto x^{1/\varepsilon}$ is a dilation in the multiplicative group $(0,\infty)$ (an exponent scaling in logarithmic coordinates), and the prefactor $1/\varepsilon$ normalizes the Jacobian, so on the Mellin side the effect is exactly the substitution $s\mapsto\varepsilon s$. The identity holds for arbitrary $\nu$ and all complex $s$ — no integrability or smoothness hypotheses — because both sides transform identically under the change of variables.
--
--   As $\varepsilon\to0^+$ the spike $\nu_\varepsilon$ concentrates at $x=1$ like an approximate identity for multiplicative convolution (when $\int_0^\infty \nu(x)\,dx/x=1$), and $\mathcal{M}(\nu_\varepsilon)(s)=\mathcal{M}\nu(\varepsilon s)\to\mathcal{M}\nu(0)=1$. This is the mechanism by which the smoothed Chebyshev function approaches the sharp one in the PNT argument.
-- source:
--   https://github.com/AlexKontorovich/PrimeNumberTheoremAnd/blob/f55e85551ac10e96d98262a354cfcaac2825f2da/PrimeNumberTheoremAnd/MellinCalculus.lean#L500-L507

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

local notation (name := mellintransform) "𝓜" => mellin
set_option backward.isDefEq.respectTransparency false

theorem MellinOfDeltaSpike (ν : ℝ → ℝ) {ε : ℝ} (εpos : ε > 0) (s : ℂ) :
    𝓜 (fun x ↦ (DeltaSpike ν ε x : ℂ)) s = 𝓜 (fun x ↦ (ν x : ℂ)) (ε * s) := by sorry
