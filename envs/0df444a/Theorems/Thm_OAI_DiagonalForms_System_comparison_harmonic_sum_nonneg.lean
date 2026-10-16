-- Prove2me | Theorems.Thm_OAI_DiagonalForms_System_comparison_harmonic_sum_nonneg
-- name    : OAI.DiagonalForms.System.comparison_harmonic_sum_nonneg
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-16T01:25:43.793986+00:00
-- url     : https://prove2.me/theorems/4335b76a-2599-4e4d-833d-7daa1764cfc7
-- title:
--   Weighted harmonic sums of positive comparison weights are comparison weights
-- statement:
--   Let $D$ be a *diagonal-form system*: index sets $P$ (parameters), $I$ (source coordinates) and $J$ (target coordinates), labelling maps $\pi : I \to P$ and $\tau : J \to P$, a complex linear space $T \subseteq \mathbb{C}^I$ of test vectors and a complex-linear map $M : T \to \mathbb{C}^J$, such that every $z \in T$ is square-summable, only finitely many parameters $\pi(i)$ occur among the indices $i$ with $z_i \neq 0$, and $T$ is closed under the multipliers $(z_i)_i \mapsto (\omega(\pi(i))\, z_i)_i$ for every $\omega : P \to \mathbb{C}$. For a weight $w : P \to \mathbb{R}$ and $z \in T$ put $S_w(z) = \sum_{i \in I} w(\pi(i))\,|z_i|^2$. The weight $w$ is called a *comparison weight* for $D$ if $\sum_{j \in F} w(\tau(j))\,|(Mz)_j|^2 \le S_w(z)$ for every $z \in T$ and every finite set $F \subseteq J$.
--
--   **Theorem.** Let $s$ be a finite index set, $c_k \ge 0$ for $k \in s$, and $w_k : P \to \mathbb{R}$ ($k \in s$) comparison weights for $D$ with $w_k(p) > 0$ for all $k \in s$ and $p \in P$. Then the weight
--   $$
--   p \longmapsto \Big( \sum_{k \in s} \frac{c_k}{w_k(p)} \Big)^{-1}
--   $$
--   is a comparison weight for $D$, with the convention $0^{-1} = 0$ (so the weight is identically $0$ when all $c_k$ vanish or $s$ is empty).
--
--   Weighted harmonic means of comparison weights are thus again comparison weights. Together with sums, nonnegative multiples and limits, this produces the logarithmic-mean and resolvent-type weights obtained later by integrating over a parameter.
--
--   **Formalization Note** The system is `OAI.DiagonalForms.System P I J` with fields `sourceParam` ($\pi$), `targetParam` ($\tau$), `tests` ($T$) and `map` ($M$); $S_w$ is `D.sourceForm w` (a `tsum`, which converges because only finitely many parameter values occur) and "comparison weight" is `D.Comparison w`. Lean's real inverse satisfies `(0 : ℝ)⁻¹ = 0`, which is what makes the degenerate case $\sum_k c_k/w_k = 0$ meaningful.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/DiagonalForms.lean#L534-L549

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

theorem OAI.DiagonalForms.System.comparison_harmonic_sum_nonneg {K : Type*} (s : Finset K)
    {w : K → P → ℝ} {c : K → ℝ}
    (hc : ∀ k ∈ s, 0 ≤ c k) (hwp : ∀ k ∈ s, ∀ p, 0 < w k p)
    (hw : ∀ k ∈ s, D.Comparison (w k)) :
    D.Comparison (fun p => (∑ k ∈ s, c k / w k p)⁻¹) := by sorry
