-- Prove2me | Theorems.Thm_OAI_AsymptoticallyMinimalLittlewood_Sampling_sample_packed
-- name    : OAI.AsymptoticallyMinimalLittlewood.Sampling.sample_packed
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T06:02:05.273905+00:00
-- url     : https://prove2.me/theorems/f279267a-8fc6-434e-a6a6-8ce34ae73fca
-- title:
--   Chirped block sampling of a bounded real torus polynomial with packed curvature arcs
-- statement:
--   Let $I$ and $J$ be finite sets, let $\mathbb{T}=\mathbb{R}/\mathbb{Z}$ be the circle, and write $e(x)=e^{2\pi i x}$ for $x\in\mathbb{R}$. Fix integer frequency vectors $a_i=(a_{ij})_{j\in J}\in\mathbb{Z}^J$ and complex coefficients $c_i\in\mathbb{C}$ for $i\in I$, and let
--
--   $$
--   F(y)=\sum_{i\in I}c_i\,e\Big(\sum_{j\in J}a_{ij}y_j\Big),\qquad y=(y_j)_{j\in J}\in\mathbb{T}^J,
--   $$
--
--   be the corresponding trigonometric polynomial on the torus $\mathbb{T}^J$. Fix further a velocity vector $v\in\mathbb{R}^J$, an integer $H\ge 1$ and real vectors $\theta_0,\dots,\theta_{H-1}\in\mathbb{R}^J$, and put
--
--   $$
--   \lambda_i=\sum_{j\in J}a_{ij}v_j,\qquad \alpha_{h,i}=\sum_{j\in J}a_{ij}\theta_{h,j}\qquad (i\in I,\ 0\le h<H).
--   $$
--
--   For $\gamma\in\mathbb{T}$ and $\ell\ge 0$ let $A(\gamma,\ell)=\{\gamma+s:\ s\in\mathbb{R},\ |s|\le \ell/2\}\subseteq\mathbb{T}$ be the closed arc of length $\ell$ centred at $\gamma$. Let $K\ge 0$ and $\delta>0$ be real numbers, and assume:
--
--   1. $F(y)$ is real and $|F(y)|\le 1$ for every $y\in\mathbb{T}^J$;
--   2. $\lambda_i\neq 0$ and $|\lambda_i|/H<1$ for every $i\in I$;
--   3. the arcs $A\big(\alpha_{h,i}\bmod 1,\ |\lambda_i|/H\big)$ are pairwise disjoint as $(h,i)$ ranges over $\{0,\dots,H-1\}\times I$;
--   4. $|c_i|/\sqrt{|\lambda_i|}\le K$ for every $i\in I$.
--
--   Then there exist real sequences $X_N=(X_N(0),\dots,X_N(N-1))$, one for each length $N\in\mathbb{N}$, and real constants $L$ and $C\ge 0$ (not depending on $N$) such that, for every $N\ge 1$ and every $t\in[0,1]$,
--
--   $$
--   \Big|\frac{1}{\sqrt N}\sum_{k=0}^{N-1}X_N(k)\,e(tk)\Big|\le K+\frac{C}{N},
--   $$
--
--   and moreover:
--
--   1. $|X_N(k)|\le 1$ for every $N\ge 1$ and every $0\le k<N$;
--   2. the mean squares converge: $\frac1N\sum_{k=0}^{N-1}X_N(k)^2\to L$ as $N\to\infty$;
--   3. $L\ge (1-\delta)\sum_{i\in I}|c_i|^2$.
--
--   This is a deterministic sampling principle. A bounded real trigonometric polynomial on a torus, together with base points whose "curvature arcs" are packed disjointly on the circle, yields bounded sequences with values in $[-1,1]$ whose asymptotic mean square is at least $(1-\delta)$ times the coefficient mass $\sum_i|c_i|^2$, while every normalized exponential sum is controlled by the coefficient-to-curvature ratio $K$ up to an $O(1/N)$ error. It is the analytic engine of the construction of nearly flat polynomials with coefficients in $[-1,1]$, which are afterwards rounded to $\pm1$ coefficients.
--
--   **Formalization Note** The family of sequences is a dependent function `X : (N : ℕ) → Fin N → ℝ`; its value at $N=0$ plays no role. Points of $\mathbb{T}^J$ are functions `J → UnitAddCircle`, the character $y\mapsto e(\sum_j a_{ij}y_j)$ is Mathlib's `mFourier (a i)`, the arc $A(\gamma,\ell)$ is `circleInterval γ ℓ`, the centres $\alpha_{h,i}$ are real numbers coerced to the circle, and $e(tk)$ is written `realPhase (2*π*t*k)` with `realPhase x = exp(i x)`. Realness of $F$ is stated as the vanishing of its imaginary part.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/Littlewood/BlockSampling.lean#L230-L339

import Mathlib
import Definitions.Def_AsymptoticallyMinimalLittlewood
import Definitions.Def_OAI_Analysis_Littlewood_Gaussian
import Definitions.Def_OAI_Analysis_Littlewood_Rounding
import Definitions.Def_OAI_Analysis_Littlewood_BinaryPacket
import Definitions.Def_OAI_Analysis_Littlewood_QuadraticTail
import Definitions.Def_OAI_Analysis_Littlewood_Spreading
import Definitions.Def_OAI_Analysis_Littlewood_ProductProbability
import Definitions.Def_OAI_Analysis_Littlewood_Nibble
import Definitions.Def_OAI_Analysis_Littlewood_Averages
import Definitions.Def_OAI_Analysis_Littlewood_FiniteRank
import Definitions.Def_OAI_Analysis_Littlewood_Chunks
import Definitions.Def_OAI_Analysis_Littlewood_DependentMoments
import Definitions.Def_OAI_Analysis_Littlewood_SlotGraph
import Definitions.Def_OAI_Analysis_Littlewood_SlotParameters
import Definitions.Def_OAI_Analysis_Littlewood_IntervalPacking
import Definitions.Def_OAI_Analysis_Littlewood_SamplingTail
import Definitions.Def_OAI_Analysis_Littlewood_SamplingEnergy
import Definitions.Def_OAI_Analysis_Littlewood_ModeSampling

open OAI OAI.AsymptoticallyMinimalLittlewood OAI.AsymptoticallyMinimalLittlewood.Sampling
universe uP uJ uI
open scoped BigOperators Topology ContDiff ComplexConjugate
open MeasureTheory Filter Complex QuadraticTail UnitAddTorus Packing

theorem OAI.AsymptoticallyMinimalLittlewood.Sampling.sample_packed {I J : Type} [Fintype I] [Fintype J]
    (a : I → J → ℤ) (c : I → ℂ) (v : J → ℝ) {H : ℕ} (hH : 1≤H)
    (θ : Fin H → J → ℝ)
    (hreal : ∀ y : J → UnitAddCircle, (∑ i, c i*mFourier (a i) y).im=0)
    (hbound : ∀ y : J → UnitAddCircle, ‖∑ i, c i*mFourier (a i) y‖≤1)
    (hlam : ∀ i, (∑ j, (a i j : ℝ)*v j)≠0)
    (hwidth : ∀ i, |∑ j, (a i j : ℝ)*v j|/(H : ℝ)<1)
    (hpack : ∀ h h' : Fin H, ∀ i i' : I, (h,i)≠(h',i') →
      Disjoint (circleInterval (((∑ j, (a i j : ℝ)*θ h j : ℝ)) : UnitAddCircle)
        (|∑ j, (a i j : ℝ)*v j|/H))
      (circleInterval (((∑ j, (a i' j : ℝ)*θ h' j : ℝ)) : UnitAddCircle)
        (|∑ j, (a i' j : ℝ)*v j|/H)))
    {K δ : ℝ} (hK : 0≤K) (hδ : 0<δ)
    (hc : ∀ i, ‖c i‖/Real.sqrt |∑ j, (a i j : ℝ)*v j|≤K) :
    ∃ X : (N : ℕ) → Fin N → ℝ, ∃ L C : ℝ,
      0≤C ∧ (1-δ)*(∑ i, ‖c i‖^2)≤L ∧
      (∀ N : ℕ, 1≤N → ∀ k, |X N k|≤1) ∧
      Tendsto (fun N : ℕ ↦ (∑ k : Fin N, (X N k)^2)/(N : ℝ)) atTop (𝓝 L) ∧
      ∀ N : ℕ, 1≤N → ∀ t∈Set.Icc (0:ℝ) 1,
        ‖(1/(Real.sqrt N : ℂ))*∑ k : Fin N, (X N k : ℂ)*realPhase (2*Real.pi*t*k)‖≤K+C/N := by sorry
