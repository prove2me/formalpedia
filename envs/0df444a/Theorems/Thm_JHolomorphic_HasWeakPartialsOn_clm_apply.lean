-- Prove2me | Theorems.Thm_JHolomorphic_HasWeakPartialsOn_clm_apply
-- name    : JHolomorphic.HasWeakPartialsOn.clm_apply
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-21T13:43:37.996798+00:00
-- url     : https://prove2.me/theorems/9d511b46-262e-4f40-88a9-7258729f839c
-- title:
--   Weak product rule for a $C^1$ family of linear maps applied to a Sobolev map
-- statement:
--   Let $U\subseteq\mathbb{C}$ be open, let $A:U\to\mathrm{L}(E,F)$ be $C^1$ on $U$, and let $w:\mathbb{C}\to E$ have weak partial derivatives $w_s,w_t$ on $U$, with $w,w_s,w_t$ integrable on every compact subset of $U$. Then $z\mapsto A(z)\,w(z)$ has weak partial derivatives $(\partial_sA)\,w+A\,w_s$ and $(\partial_tA)\,w+A\,w_t$ on $U$, where $\partial_sA(z)=DA(z)\,1$ and $\partial_tA(z)=DA(z)\,i$.
--
--   **Formalization Note** $E$ (and $F$) are finite-dimensional real normed spaces and $U\subseteq\mathbb{C}$ is open. $A$ is `ℂ → E →L[ℝ] F` with `ContDiffOn ℝ 1 A U`; $\partial_sA(z)$ is `fderiv ℝ A z 1` and $\partial_tA(z)$ is `fderiv ℝ A z Complex.I`. Weak partial derivatives are in the sense of `HasWeakPartialsOn` (testing against real $C^\infty$ functions with compact support in $U$, Bochner integrals over $\mathbb{C}$), and "almost every $z\in U$" is `∀ᵐ z ∂(volume.restrict U)`.
-- source:
--   Standard (weak derivatives and distribution theory).

import Definitions.Def_JHolomorphic_Setting
import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.ContDiff.Comp

namespace JHolomorphic

open MeasureTheory Filter Topology
open scoped ContDiff

/-- Weak Leibniz rule: if `w` has weak partials `wₛ`, `wₜ` on an open set `U` and `A` is a `C¹`
family of linear maps on `U`, then `z ↦ A(z) w(z)` has weak partials
`(∂ₛA) w + A wₛ` and `(∂ₜA) w + A wₜ` on `U`. -/
theorem HasWeakPartialsOn.clm_apply {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    {U : Set ℂ} (hU : IsOpen U) {A : ℂ → E →L[ℝ] F} (hA : ContDiffOn ℝ 1 A U)
    {w ws wt : ℂ → E} (hw : HasWeakPartialsOn U w ws wt)
    (hint : ∀ K ⊆ U, IsCompact K →
      IntegrableOn w K ∧ IntegrableOn ws K ∧ IntegrableOn wt K) :
    HasWeakPartialsOn U (fun z => A z (w z)) (fun z => fderiv ℝ A z 1 (w z) + A z (ws z))
      (fun z => fderiv ℝ A z Complex.I (w z) + A z (wt z)) := by
  sorry

end JHolomorphic
