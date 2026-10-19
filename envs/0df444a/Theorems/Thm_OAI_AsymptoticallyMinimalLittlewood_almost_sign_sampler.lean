-- Prove2me | Theorems.Thm_OAI_AsymptoticallyMinimalLittlewood_almost_sign_sampler
-- name    : OAI.AsymptoticallyMinimalLittlewood.almost_sign_sampler
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T06:05:14.660835+00:00
-- url     : https://prove2.me/theorems/e700fda8-a18a-4687-b331-e00a3cd14c3e
-- title:
--   Almost-sign sequences in $[-1,1]$ with nearly flat exponential sums
-- statement:
--   Let $\delta$ be a real number with $0<\delta<1/20$, and write $e(x)=e^{2\pi i x}$ for $x\in\mathbb{R}$. Then there exist real sequences $X_N=(X_N(0),\dots,X_N(N-1))$, one for each length $N\in\mathbb{N}$, and real constants $L$ and $C\ge 0$ (not depending on $N$) such that, for every $N\ge1$ and every $t\in[0,1]$,
--
--   $$
--   \Big|\frac{1}{\sqrt N}\sum_{k=0}^{N-1}X_N(k)\,e(tk)\Big|\le\sqrt{\frac{(1+\delta)^3}{1-\delta}}+\frac{C}{N},
--   $$
--
--   and moreover:
--
--   1. $|X_N(k)|\le 1$ for every $N\ge1$ and every $0\le k<N$;
--   2. the mean squares converge: $\frac1N\sum_{k=0}^{N-1}X_N(k)^2\to L$ as $N\to\infty$;
--   3. $L\ge 1-7\delta$.
--
--   In other words, the polynomials $Q_N(z)=\sum_{k=0}^{N-1}X_N(k)z^k$ have real coefficients in $[-1,1]$ with asymptotic mean square at least $1-7\delta$, and satisfy $|Q_N(z)|\le\sqrt{(1+\delta)^3/(1-\delta)}\,\sqrt N+C/\sqrt N$ for every $z$ on the unit circle.
--
--   This is the relaxed ("almost sign") form of the existence of flat Littlewood polynomials. Since $\sqrt{(1+\delta)^3/(1-\delta)}\to1$ as $\delta\to0$, it supplies, for small $\delta$, coefficient sequences in $[-1,1]$ that are close to $\pm1$ in mean square and whose polynomials have size at most $(1+O(\delta))\sqrt N$ uniformly on the unit circle. A separate rounding step then replaces the $X_N(k)$ by genuine signs.
--
--   **Formalization Note** The family of sequences is a dependent function `X : (N : ℕ) → Fin N → ℝ`; its value at $N=0$ plays no role. The exponential $e(tk)$ is written `realPhase (2*π*t*k)` with `realPhase x = exp(i x)`, and the mean-square limit is a `Tendsto` statement along `atTop` for the real numbers $\frac1N\sum_k X_N(k)^2$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/Littlewood/AlmostSign.lean#L10-L107

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

open OAI OAI.AsymptoticallyMinimalLittlewood
open scoped BigOperators Topology ContDiff ComplexConjugate
open MeasureTheory Filter Complex UnitAddTorus

theorem OAI.AsymptoticallyMinimalLittlewood.almost_sign_sampler {δ : ℝ} (hδ : 0<δ) (hδ20 : δ<1/20) :
    ∃ X : (N : ℕ) → Fin N → ℝ, ∃ L C : ℝ,
      0≤C ∧ 1-7*δ≤L ∧
      (∀ N : ℕ, 1≤N → ∀ k, |X N k|≤1) ∧
      Tendsto (fun N : ℕ ↦ (∑ k : Fin N, (X N k)^2)/(N : ℝ)) atTop (𝓝 L) ∧
      ∀ N : ℕ, 1≤N → ∀ t∈Set.Icc (0:ℝ) 1,
        ‖(1/(Real.sqrt N : ℂ))*∑ k : Fin N, (X N k : ℂ)*realPhase (2*Real.pi*t*k)‖≤
          Real.sqrt ((1+δ)^3/(1-δ))+C/N := by sorry
