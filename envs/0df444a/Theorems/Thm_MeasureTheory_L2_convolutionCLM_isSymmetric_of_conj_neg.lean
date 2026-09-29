-- Prove2me | Theorems.Thm_MeasureTheory_L2_convolutionCLM_isSymmetric_of_conj_neg
-- name    : MeasureTheory.L2.convolutionCLM_isSymmetric_of_conj_neg
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:12.429051+00:00
-- url     : https://prove2.me/theorems/f7acdc05-a79d-5e62-9e62-4744e92d9ee6
-- title:
--   Convolution by a Hermitian kernel is symmetric on L²(G)
-- statement:
--   Let $G$ be a compact Hausdorff abelian topological group, equipped with its Borel $\sigma$-algebra and viewed as a topological additive group, and let $\mu$ be a measure on $G$ that is an additive Haar measure and is finite. Let $f \colon G \to \mathbb{C}$ be continuous and Hermitian in the sense that $f(-x) = \overline{f(x)}$ for every $x \in G$. Let $T \colon L^2(\mu) \to L^2(\mu)$ be a continuous $\mathbb{C}$-linear operator on the complex $L^2$ space of $\mu$ such that, for every $\varphi \in L^2(\mu)$, a representative of $T\varphi$ agrees $\mu$-almost everywhere with the convolution of $f$ and a representative of $\varphi$ formed with respect to $\mu$ and the multiplication bilinear map on $\mathbb{C}$, i.e. with $x \mapsto \int_G f(t)\,\varphi(x-t)\,d\mu(t)$. The conclusion is that the underlying $\mathbb{C}$-linear map of $T$ is symmetric: $\langle T\varphi, \psi\rangle = \langle \varphi, T\psi\rangle$ for all $\varphi, \psi \in L^2(\mu)$.
--
--   This is the self-adjointness half of the statement that convolution by a Hermitian continuous kernel on a compact abelian group is a compact self-adjoint operator on $L^2$; it is used by [`MeasureTheory.L2.exists_convolutionCLM_isCompactOperator_of_compactSpace`](thm.html#MeasureTheory.L2.exists_convolutionCLM_isCompactOperator_of_compactSpace), and thereby makes the spectral theory of compact self-adjoint operators available for producing eigenfunctions of convolution operators.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_MeasureTheory_L2_convolutionCLM_isSymmetric_of_conj_neg.lean

import Mathlib.Analysis.Convolution
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Measure.Haar.Basic
import Mathlib.Analysis.InnerProductSpace.Symmetric
import Mathlib.Analysis.Normed.Operator.Mul

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open scoped Convolution

theorem MeasureTheory.L2.convolutionCLM_isSymmetric_of_conj_neg
    (G : Type*) [MeasurableSpace G] [AddCommGroup G] [TopologicalSpace G]
    [IsTopologicalAddGroup G] [CompactSpace G] [T2Space G] [BorelSpace G]
    (μ : MeasureTheory.Measure G) [μ.IsAddHaarMeasure] [MeasureTheory.IsFiniteMeasure μ]
    (f : C(G, ℂ)) (hf : ∀ x, f (-x) = star (f x))
    (T : MeasureTheory.Lp ℂ 2 μ →L[ℂ] MeasureTheory.Lp ℂ 2 μ)
    (hT : ∀ φ : MeasureTheory.Lp ℂ 2 μ, (T φ : G → ℂ) =ᵐ[μ]
      ((f : G → ℂ) ⋆[ContinuousLinearMap.mul ℂ ℂ, μ] (φ : G → ℂ))) :
    LinearMap.IsSymmetric (T : MeasureTheory.Lp ℂ 2 μ →ₗ[ℂ] MeasureTheory.Lp ℂ 2 μ) := by sorry
