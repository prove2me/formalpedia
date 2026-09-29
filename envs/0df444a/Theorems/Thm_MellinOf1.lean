-- Prove2me | Theorems.Thm_MellinOf1
-- name    : MellinOf1
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-07-29T15:34:25.002271+00:00
-- url     : https://prove2.me/theorems/29bc4158-3009-45bc-b20c-644bab675f39
-- title:
--   Mellin transform of the unit-interval cutoff: $\mathcal{M}(\mathbf{1}_{(0,1]})(s)=1/s$ for $\operatorname{Re} s>0$
-- statement:
--   Let $s\in\mathbb{C}$ with $\operatorname{Re} s>0$. The Mellin transform of the indicator function of the interval $(0,1]$ — the function equal to $1$ when $0<x\le 1$ and $0$ otherwise — is
--
--   $$\mathcal{M}\bigl(\mathbf{1}_{(0,1]}\bigr)(s) \;=\; \int_0^{1} x^{s-1}\,dx \;=\; \frac{1}{s}.$$
--
--   The computation is the elementary evaluation of $\int_0^1 x^{s-1}dx$, convergent precisely because $\operatorname{Re} s>0$.
--
--   Despite its simplicity this identity is the seed of the whole Perron/mollification machinery: the sharp cutoff $\mathbf{1}_{(0,1]}$ is what truncates the sum $\sum_n \Lambda(n)$ at $n\le X$, and its Mellin transform $1/s$ is the factor appearing in Perron's formula. Convolving the cutoff with a delta-spike mollifier multiplies this $1/s$ by $\mathcal{M}\nu(\varepsilon s)$, giving the smoothed integrand actually used in the contour argument for the Prime Number Theorem.
-- source:
--   https://github.com/AlexKontorovich/PrimeNumberTheoremAnd/blob/f55e85551ac10e96d98262a354cfcaac2825f2da/PrimeNumberTheoremAnd/MellinCalculus.lean#L543-L546

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

theorem MellinOf1 (s : ℂ) (h : s.re > 0) :
    𝓜 ((fun x ↦ if 0 < x ∧ x ≤ 1 then 1 else 0)) s = 1 / s := by sorry
