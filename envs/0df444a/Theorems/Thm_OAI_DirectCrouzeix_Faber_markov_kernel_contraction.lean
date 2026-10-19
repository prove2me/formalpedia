-- Prove2me | Theorems.Thm_OAI_DirectCrouzeix_Faber_markov_kernel_contraction
-- name    : OAI.DirectCrouzeix.Faber.markov_kernel_contraction
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T05:49:34.369336+00:00
-- url     : https://prove2.me/theorems/86f6946f-3807-4def-922a-2ef8743992a5
-- title:
--   Nonnegative kernels with unit marginals are $L^2$ contractions for Hilbert-space-valued functions
-- statement:
--   Let $X$ and $Y$ be compact, second countable metric spaces with their Borel $\sigma$-algebras, and let $\mu$ on $X$ and $\nu$ on $Y$ be finite Borel measures. Let $E$ be a real Hilbert space. Let $K:X\times Y\to\mathbb{R}$ be jointly continuous with $K(x,y)\ge0$ for all $x\in X$, $y\in Y$, and assume that both marginals of $K$ are identically $1$:
--   $$
--   \int_X K(x,y)\,d\mu(x)=1\ \ \text{for every }y\in Y,\qquad \int_Y K(x,y)\,d\nu(y)=1\ \ \text{for every }x\in X.
--   $$
--   Then every continuous $u:X\to E$ satisfies
--   $$
--   \int_Y\Big\|\int_X K(x,y)\,u(x)\,d\mu(x)\Big\|^2\,d\nu(y)\;\le\;\int_X\|u(x)\|^2\,d\mu(x).
--   $$
--
--   In operator language, the integral operator $(Tu)(y)=\int_X K(x,y)\,u(x)\,d\mu(x)$ with a nonnegative kernel whose column and row integrals equal $1$ does not increase the $L^2$ norm of continuous $E$-valued functions; this is a vector-valued Schur test with constant $1$. In the development it is applied on $\mathbb{T}\times\mathbb{T}$, $\mathbb{T}=\mathbb{R}/\mathbb{Z}$, with a nonnegative boundary kernel, to bound the boundary energy of a Faber remainder by the energy of a trigonometric polynomial.
--
--   **Formalization Note** The integrals are Bochner integrals in $E$ and in $\mathbb{R}$; continuity on compact spaces and finiteness of $\mu,\nu$ make every integrand integrable. Second countability and the Borel structure are separate typeclass hypotheses (`SecondCountableTopology`, `BorelSpace`); second countability is automatic for compact metric spaces. The space $E$ is a real inner product space that is complete.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/DirectCrouzeix/KernelContraction.lean#L65-L95

import Mathlib
import Definitions.Def_DirectCrouzeix
import Definitions.Def_OAI_Analysis_DirectCrouzeix_PositiveBlocks
import Definitions.Def_OAI_Analysis_DirectCrouzeix_Resolvent
import Definitions.Def_OAI_Analysis_DirectCrouzeix_PolynomialCalculus
import Definitions.Def_OAI_Analysis_DirectCrouzeix_HilbertSchmidt
import Definitions.Def_OAI_Analysis_DirectCrouzeix_SingularPairs
import Definitions.Def_OAI_Analysis_DirectCrouzeix_Sharpness
import Definitions.Def_OAI_Analysis_DirectCrouzeix_CircleFourier
import Definitions.Def_OAI_Analysis_DirectCrouzeix_BoundaryEnergy
import Definitions.Def_OAI_Analysis_DirectCrouzeix_PolynomialEnergy
import Definitions.Def_OAI_Analysis_DirectCrouzeix_CompactIntegrals
import Definitions.Def_OAI_Analysis_DirectCrouzeix_DividedDifferences
import Definitions.Def_OAI_Analysis_DirectCrouzeix_TaylorFourier
import Definitions.Def_OAI_Analysis_DirectCrouzeix_FaberPolynomials
import Definitions.Def_OAI_Analysis_DirectCrouzeix_BoundaryKernel
import Definitions.Def_OAI_Analysis_DirectCrouzeix_KernelContraction

open OAI OAI.DirectCrouzeix OAI.DirectCrouzeix.Faber
universe u_117 u_118 u_119 u_120 u_121 u_122 u_123 u_124 u_125 u_126 u_127 u_128
open scoped Matrix Matrix.Norms.L2Operator Kronecker
open MeasureTheory Set Filter Metric
open scoped Topology Interval ENNReal NNReal ComplexConjugate

theorem OAI.DirectCrouzeix.Faber.markov_kernel_contraction {α : Type u_124} {β : Type u_125} {E : Type u_126}
    [MetricSpace α] [MeasurableSpace α] [BorelSpace α] [CompactSpace α]
    [SecondCountableTopology α]
    [MetricSpace β] [MeasurableSpace β] [BorelSpace β] [CompactSpace β]
    [SecondCountableTopology β]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (μ : Measure α) (ν : Measure β) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (K : α → β → ℝ) (u : α → E)
    (hK : Continuous K.uncurry) (hu : Continuous u)
    (hpos : ∀ x y, 0 ≤ K x y)
    (hcol : ∀ y, ∫ x, K x y ∂μ = 1)
    (hrow : ∀ x, ∫ y, K x y ∂ν = 1) :
    (∫ y, ‖∫ x, K x y • u x ∂μ‖ ^ 2 ∂ν) ≤ ∫ x, ‖u x‖ ^ 2 ∂μ := by sorry
