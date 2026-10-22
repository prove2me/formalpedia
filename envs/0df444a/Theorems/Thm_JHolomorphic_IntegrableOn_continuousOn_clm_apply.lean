-- Prove2me | Theorems.Thm_JHolomorphic_IntegrableOn_continuousOn_clm_apply
-- name    : JHolomorphic.IntegrableOn.continuousOn_clm_apply
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-21T13:44:12.164267+00:00
-- url     : https://prove2.me/theorems/ec052d5d-77d2-421e-bc34-b3bbd91b122c
-- title:
--   A continuous family of linear maps applied to an integrable map is integrable on a compact set
-- statement:
--   Let $K\subseteq\mathbb{C}$ be compact, let $A:\mathbb{C}\to\mathrm{L}(E,F)$ be continuous on $K$ and let $f:\mathbb{C}\to E$ be integrable on $K$. Then $z\mapsto A(z)\,f(z)$ is integrable on $K$.
--
--   **Formalization Note** $E,F$ are finite-dimensional real normed spaces; $A$ is `ℂ → E →L[ℝ] F`; integrability is `IntegrableOn · K` for Lebesgue measure.
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

/-- If `A` is a continuous family of linear maps on a compact set `K` and `f` is integrable on
`K`, then `z ↦ A(z) f(z)` is integrable on `K`. -/
theorem IntegrableOn.continuousOn_clm_apply {E F : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    [FiniteDimensional ℝ F] {K : Set ℂ} (hK : IsCompact K) {A : ℂ → E →L[ℝ] F}
    (hA : ContinuousOn A K) {f : ℂ → E} (hf : IntegrableOn f K) :
    IntegrableOn (fun z => A z (f z)) K := by
  sorry

end JHolomorphic
