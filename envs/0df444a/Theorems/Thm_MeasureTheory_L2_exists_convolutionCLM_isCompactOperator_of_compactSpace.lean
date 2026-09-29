-- Prove2me | Theorems.Thm_MeasureTheory_L2_exists_convolutionCLM_isCompactOperator_of_compactSpace
-- name    : MeasureTheory.L2.exists_convolutionCLM_isCompactOperator_of_compactSpace
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:12.429051+00:00
-- url     : https://prove2.me/theorems/b4b789f8-1e81-5087-ba89-9a6b3bef55f0
-- title:
--   Convolution by a Hermitian continuous kernel is compact and symmetric
-- statement:
--   Let $G$ be a type carrying a measurable space structure, an additive commutative group structure and a topology making it a topological additive group, assumed compact and Hausdorff, with the measurable structure being the Borel structure of the topology. Let $\mu$ be a measure on $G$ which is an additive Haar measure and is finite, and let $f : C(G,\mathbb{C})$ be a continuous complex-valued function satisfying $f(-x) = \overline{f(x)}$ for every $x \in G$. The assertion is the existence of a continuous $\mathbb{C}$-linear operator $T$ on $L^2(G,\mu)$ (the Lean space `MeasureTheory.Lp ℂ 2 μ`) with three properties: for every $\varphi \in L^2(G,\mu)$, a representative of $T\varphi$ agrees $\mu$-almost everywhere with the convolution of $f$ and a representative of $\varphi$, the convolution being formed with respect to $\mu$ and the bilinear multiplication map of $\mathbb{C}$; $T$ is a compact operator in the sense of `IsCompactOperator`, i.e. some neighbourhood of $0$ has image contained in a compact set; and the underlying linear map of $T$ is symmetric, i.e. $\langle T\varphi, \psi\rangle = \langle \varphi, T\psi\rangle$ for all $\varphi, \psi$.
--
--   This is the analytic input to the Peter–Weyl theorem for compact abelian groups: convolution by a continuous Hermitian kernel on $L^2$ of a compact group is a compact self-adjoint operator, so that the spectral theorem applies to it. It is used in the construction of continuous characters separating points of a compact abelian group, and from there in the cuspidality arguments of the Langlands–Tunnell step.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_MeasureTheory_L2_exists_convolutionCLM_isCompactOperator_of_compactSpace.lean

import Mathlib.Analysis.Convolution
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Measure.Haar.Basic
import Mathlib.Analysis.Normed.Operator.Compact.Basic
import Mathlib.Analysis.InnerProductSpace.Symmetric
import Mathlib.Analysis.Normed.Operator.Mul

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open scoped Convolution

theorem MeasureTheory.L2.exists_convolutionCLM_isCompactOperator_of_compactSpace
    (G : Type*) [MeasurableSpace G] [AddCommGroup G] [TopologicalSpace G]
    [IsTopologicalAddGroup G] [CompactSpace G] [T2Space G] [BorelSpace G]
    (μ : MeasureTheory.Measure G) [μ.IsAddHaarMeasure] [MeasureTheory.IsFiniteMeasure μ]
    (f : C(G, ℂ)) (hf : ∀ x, f (-x) = star (f x)) :
    ∃ T : MeasureTheory.Lp ℂ 2 μ →L[ℂ] MeasureTheory.Lp ℂ 2 μ,
      (∀ φ : MeasureTheory.Lp ℂ 2 μ, (T φ : G → ℂ) =ᵐ[μ]
        ((f : G → ℂ) ⋆[ContinuousLinearMap.mul ℂ ℂ, μ] (φ : G → ℂ))) ∧
      IsCompactOperator T ∧ LinearMap.IsSymmetric (T : MeasureTheory.Lp ℂ 2 μ →ₗ[ℂ] MeasureTheory.Lp ℂ 2 μ) := by sorry
