-- Prove2me | Theorems.Thm_OAI_DiagonalForms_System_comparison_logMean
-- name    : OAI.DiagonalForms.System.comparison_logMean
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-16T01:29:11.762088+00:00
-- url     : https://prove2.me/theorems/bd19ac46-b719-4fe4-91ab-03a22b729f43
-- title:
--   The logarithmic mean of two positive comparison weights is a comparison weight
-- statement:
--   Let $D$ be a *diagonal-form system*: index sets $P$ (parameters), $I$ (source coordinates) and $J$ (target coordinates), labelling maps $\pi : I \to P$ and $\tau : J \to P$, a complex linear space $T \subseteq \mathbb{C}^I$ of test vectors and a complex-linear map $M : T \to \mathbb{C}^J$, such that every $z \in T$ is square-summable, only finitely many parameters $\pi(i)$ occur among the indices $i$ with $z_i \neq 0$, and $T$ is closed under the multipliers $(z_i)_i \mapsto (\omega(\pi(i))\, z_i)_i$ for every $\omega : P \to \mathbb{C}$. For a weight $w : P \to \mathbb{R}$ and $z \in T$ put $S_w(z) = \sum_{i \in I} w(\pi(i))\,|z_i|^2$. The weight $w$ is called a *comparison weight* for $D$ if $\sum_{j \in F} w(\tau(j))\,|(Mz)_j|^2 \le S_w(z)$ for every $z \in T$ and every finite set $F \subseteq J$.
--
--   For $X, Y > 0$ let $L(X,Y)$ denote the logarithmic mean, $L(X,Y) = \dfrac{Y - X}{\log Y - \log X}$ for $X \neq Y$ and $L(X,X) = X$.
--
--   **Theorem.** If $v, w : P \to \mathbb{R}$ are comparison weights for $D$ with $v(p) > 0$ and $w(p) > 0$ for all $p$, then
--   $$
--   p \longmapsto L\big(v(p), w(p)\big)
--   $$
--   is a comparison weight for $D$.
--
--   The logarithmic mean lies between the harmonic-type parallel sums and the arithmetic mean; this lemma shows that the comparison property is stable under it. Logarithmic means of weights arise naturally when comparing quadratic forms built from logarithms of density-matrix eigenvalues.
--
--   **Formalization Note** The system is `OAI.DiagonalForms.System P I J` with fields `sourceParam` ($\pi$), `targetParam` ($\tau$), `tests` ($T$) and `map` ($M$); $S_w$ is `D.sourceForm w` (a `tsum`, which converges because only finitely many parameter values occur) and "comparison weight" is `D.Comparison w`. $L$ is `logMean`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/DiagonalForms.lean#L615-L632

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
open MeasureTheory Set
variable {P I J : Type*} (D : DiagonalForms.System P I J)

theorem OAI.DiagonalForms.System.comparison_logMean {v w : P → ℝ}
    (hv : D.Comparison v) (hw : D.Comparison w)
    (hvp : ∀ p, 0 < v p) (hwp : ∀ p, 0 < w p) :
    D.Comparison (fun p => logMean (v p) (w p)) := by sorry
