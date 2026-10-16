-- Prove2me | Theorems.Thm_OAI_DiagonalForms_System_comparison_inverse_integral
-- name    : OAI.DiagonalForms.System.comparison_inverse_integral
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-16T01:26:13.833137+00:00
-- url     : https://prove2.me/theorems/d6af1864-9ab1-4667-88d3-e15f87d637ff
-- title:
--   The inverse of the integral of inverse comparison weights over a compact parameter space is a comparison weight
-- statement:
--   Let $D$ be a *diagonal-form system*: index sets $P$ (parameters), $I$ (source coordinates) and $J$ (target coordinates), labelling maps $\pi : I \to P$ and $\tau : J \to P$, a complex linear space $T \subseteq \mathbb{C}^I$ of test vectors and a complex-linear map $M : T \to \mathbb{C}^J$, such that every $z \in T$ is square-summable, only finitely many parameters $\pi(i)$ occur among the indices $i$ with $z_i \neq 0$, and $T$ is closed under the multipliers $(z_i)_i \mapsto (\omega(\pi(i))\, z_i)_i$ for every $\omega : P \to \mathbb{C}$. For a weight $w : P \to \mathbb{R}$ and $z \in T$ put $S_w(z) = \sum_{i \in I} w(\pi(i))\,|z_i|^2$. The weight $w$ is called a *comparison weight* for $D$ if $\sum_{j \in F} w(\tau(j))\,|(Mz)_j|^2 \le S_w(z)$ for every $z \in T$ and every finite set $F \subseteq J$.
--
--   **Theorem.** Let $K$ be a compact metric space with its Borel $\sigma$-algebra, $\mu$ a finite measure on $K$ with $\mu \neq 0$, and $k_0 \in K$. Let $w : K \times P \to \mathbb{R}$, $(k,p) \mapsto w_k(p)$, satisfy: $k \mapsto w_k(p)$ is continuous for each $p$, $w_k(p) > 0$ for all $k, p$, and each $w_k$ is a comparison weight for $D$. Then
--   $$
--   p \longmapsto \Big( \int_K \frac{d\mu(k)}{w_k(p)} \Big)^{-1}
--   $$
--   is a comparison weight for $D$.
--
--   This is the continuous version of the harmonic-sum closure property: a $\mu$-weighted harmonic mean of a continuous family of comparison weights is again a comparison weight. With $K = [0,1]$ and affine families it yields logarithmic-mean and resolvent-type weights.
--
--   **Formalization Note** The system is `OAI.DiagonalForms.System P I J` with fields `sourceParam` ($\pi$), `targetParam` ($\tau$), `tests` ($T$) and `map` ($M$); $S_w$ is `D.sourceForm w` (a `tsum`, which converges because only finitely many parameter values occur) and "comparison weight" is `D.Comparison w`. The point $k_0$ is only used to build the simple-function approximations `compactApprox k₀ n` in the proof.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/DiagonalForms.lean#L551-L577

import Mathlib
import Definitions.Def_EntropyPhotonNumber
import Definitions.Def_OAI_MathematicalPhysics_Fock_Beam
import Definitions.Def_OAI_Analysis_QuantumTrace_Basic
import Definitions.Def_OAI_MathematicalPhysics_Fock_Operators
import Definitions.Def_OAI_InformationTheory_PhotonNumber_Gibbs
import Definitions.Def_OAI_Analysis_TensorLp
import Definitions.Def_OAI_InformationTheory_PhotonNumber_BeamTrace
import Definitions.Def_OAI_InformationTheory_PhotonNumber_Functions
import Definitions.Def_OAI_Analysis_DiagonalForms

open OAI OAI.DiagonalForms OAI.DiagonalForms.System
open scoped BigOperators ComplexConjugate ENNReal Topology
open MeasureTheory
open scoped ComplexConjugate
open scoped BigOperators ComplexConjugate
open scoped BigOperators
open MvPolynomial
open scoped BigOperators ComplexConjugate Classical
open Submodule
open ContinuousLinearMap
open scoped ENNReal
open Set Filter Topology Complex MeasureTheory
open Set Filter Topology Complex Metric
open MeasureTheory Set Filter Topology Complex Metric InnerProductSpace
open scoped ENNReal NNReal
open Filter Topology
open MeasureTheory
variable {P I J : Type*} (D : DiagonalForms.System P I J)

theorem OAI.DiagonalForms.System.comparison_inverse_integral {K : Type*} [MetricSpace K] [CompactSpace K]
    [MeasurableSpace K] [BorelSpace K] (μ : Measure K) [IsFiniteMeasure μ]
    (k₀ : K) (hμ : μ ≠ 0) {w : K → P → ℝ}
    (hcont : ∀ p, Continuous (fun k => w k p)) (hwp : ∀ k p, 0 < w k p)
    (hw : ∀ k, D.Comparison (w k)) :
    D.Comparison (fun p => (∫ k, (w k p)⁻¹ ∂μ)⁻¹) := by sorry
