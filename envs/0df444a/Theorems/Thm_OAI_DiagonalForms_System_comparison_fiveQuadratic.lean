-- Prove2me | Theorems.Thm_OAI_DiagonalForms_System_comparison_fiveQuadratic
-- name    : OAI.DiagonalForms.System.comparison_fiveQuadratic
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-16T01:30:45.485978+00:00
-- url     : https://prove2.me/theorems/58cb50b0-f1ca-4041-b289-3e256deca7f1
-- title:
--   Comparison weights from a five-term quadratic minorant whose minimum is attained along a multiplier
-- statement:
--   Let $D$ be a *diagonal-form system*: index sets $P$ (parameters), $I$ (source coordinates) and $J$ (target coordinates), labelling maps $\pi : I \to P$ and $\tau : J \to P$, a complex linear space $T \subseteq \mathbb{C}^I$ of test vectors and a complex-linear map $M : T \to \mathbb{C}^J$, such that every $z \in T$ is square-summable, only finitely many parameters $\pi(i)$ occur among the indices $i$ with $z_i \neq 0$, and $T$ is closed under the multipliers $(z_i)_i \mapsto (\omega(\pi(i))\, z_i)_i$ for every $\omega : P \to \mathbb{C}$. For a weight $w : P \to \mathbb{R}$ and $z \in T$ put $S_w(z) = \sum_{i \in I} w(\pi(i))\,|z_i|^2$. The weight $w$ is called a *comparison weight* for $D$ if $\sum_{j \in F} w(\tau(j))\,|(Mz)_j|^2 \le S_w(z)$ for every $z \in T$ and every finite set $F \subseteq J$.
--
--   For real numbers $v_0, \dots, v_4$ and $\xi, \varphi \in \mathbb{C}$ put
--   $$
--   Q_{v}(\xi,\varphi) = v_0|\xi - \varphi|^2 + v_1|\xi + \varphi|^2 + v_2|\xi + \varphi|^2 + v_3|\xi - \varphi|^2 + v_4|\varphi|^2 .
--   $$
--
--   **Theorem.** Let $v_0, \dots, v_4 : P \to \mathbb{R}$ be comparison weights for $D$, and let $F, \delta : P \to \mathbb{R}$ satisfy, for every $p \in P$ and all $\xi, \varphi \in \mathbb{C}$ (writing $v(p) = (v_0(p), \dots, v_4(p))$):
--
--   1. (attained minimum) $Q_{v(p)}\big(\xi, \delta(p)\xi\big) = F(p)\,|\xi|^2$;
--   2. (lower bound) $F(p)\,|\xi|^2 \le Q_{v(p)}(\xi, \varphi)$.
--
--   Then $F$ is a comparison weight for $D$.
--
--   In words: if $F(p)|\xi|^2$ is the minimum over $\varphi$ of a quadratic form built from comparison weights, and the minimizer is the linear multiplier $\varphi = \delta(p)\xi$, then $F$ is itself a comparison weight. No positivity of $F$ or of the $v_i$ is assumed. The lemma is a variational way to certify comparison weights given by more complicated closed-form expressions.
--
--   **Formalization Note** The system is `OAI.DiagonalForms.System P I J` with fields `sourceParam` ($\pi$), `targetParam` ($\tau$), `tests` ($T$) and `map` ($M$); $S_w$ is `D.sourceForm w` (a `tsum`, which converges because only finitely many parameter values occur) and "comparison weight" is `D.Comparison w`. $Q_v$ is `fiveQuadratic v₀ v₁ v₂ v₃ v₄ ξ φ`, and $|\cdot|^2$ is `Complex.normSq`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/DiagonalForms.lean#L856-L900

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
open Function
variable {P I J : Type*} (D : DiagonalForms.System P I J)

theorem OAI.DiagonalForms.System.comparison_fiveQuadratic {v₀ v₁ v₂ v₃ v₄ F δ : P → ℝ}
    (h₀ : D.Comparison v₀) (h₁ : D.Comparison v₁) (h₂ : D.Comparison v₂)
    (h₃ : D.Comparison v₃) (h₄ : D.Comparison v₄)
    (hmin : ∀ p ξ, fiveQuadratic (v₀ p) (v₁ p) (v₂ p) (v₃ p) (v₄ p)
      ξ ((δ p : ℂ)*ξ) = F p*Complex.normSq ξ)
    (hlower : ∀ p ξ φ, F p*Complex.normSq ξ ≤
      fiveQuadratic (v₀ p) (v₁ p) (v₂ p) (v₃ p) (v₄ p) ξ φ) :
    D.Comparison F := by sorry
