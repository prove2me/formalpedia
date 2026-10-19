-- Prove2me | Theorems.Thm_OAI_AsymptoticallyMinimalLittlewood_round_sample_once
-- name    : OAI.AsymptoticallyMinimalLittlewood.round_sample_once
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T06:05:53.873999+00:00
-- url     : https://prove2.me/theorems/94af298a-8bb9-43be-a845-80c63d227e16
-- title:
--   Rounding an almost-sign sequence to a nearly flat Littlewood polynomial
-- statement:
--   Let $N\ge1$ be an integer, let $\delta$ be a real number with $0<\delta<1/20$, let $K$ and $C$ be arbitrary real numbers, and write $e(x)=e^{2\pi i x}$ for $x\in\mathbb{R}$. Let $X_0,\dots,X_{N-1}$ be real numbers such that
--
--   1. $|X_k|\le1$ for every $k$;
--   2. $\sum_{k=0}^{N-1}X_k^2\ge(1-8\delta)N$;
--   3. for every $t\in[0,1]$, $\Big|\frac{1}{\sqrt N}\sum_{k=0}^{N-1}X_k\,e(tk)\Big|\le K+\frac CN$.
--
--   Then there are signs $\varepsilon_0,\dots,\varepsilon_{N-1}\in\{-1,1\}$ such that the Littlewood polynomial $P_\varepsilon(z)=\sum_{k=0}^{N-1}\varepsilon_kz^k$ satisfies, for every complex number $z$ with $|z|=1$,
--
--   $$
--   \frac{|P_\varepsilon(z)|}{\sqrt N}\le K+\frac CN+196608\left(\frac{1}{\sqrt N}+2\sqrt{\delta\log(20/\delta)}\right),
--   $$
--
--   where $\log$ denotes the natural logarithm.
--
--   This is the rounding step in the construction of flat Littlewood polynomials: a relaxed solution, i.e. coefficients in $[-1,1]$ with mean square at least $1-8\delta$ and nearly flat polynomial on the unit circle, is converted into a genuine $\pm1$ polynomial at the cost of an additive loss $O(N^{-1/2})+O\big(\sqrt{\delta\log(20/\delta)}\big)$ in the normalized supremum, which tends to $0$ as $N\to\infty$ and $\delta\to0$.
--
--   **Formalization Note** The signs form a real vector `ε : Fin N → ℝ` with every entry equal to $-1$ or $1$ (`IsRealSigning ε`), and $P_\varepsilon(z)$ is `littlewoodValue ε z`. The exponential $e(tk)$ is written `realPhase (2*π*t*k)` with `realPhase x = exp(i x)`. No sign conditions are imposed on $K$ and $C$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/Littlewood/Main.lean#L130-L177

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
open scoped BigOperators Topology
open Filter

theorem OAI.AsymptoticallyMinimalLittlewood.round_sample_once {N : ℕ} (hN : 1≤N) {δ K C : ℝ}
    (hδ : 0<δ) (hδ20 : δ<1/20) (X : Fin N → ℝ)
    (hX : ∀ k, |X k|≤1)
    (hE : (1-8*δ)*(N : ℝ)≤∑ k, (X k)^2)
    (hmax : ∀ t∈Set.Icc (0:ℝ) 1,
      ‖(1/(Real.sqrt N : ℂ))*∑ k : Fin N, (X k : ℂ)*realPhase (2*Real.pi*t*k)‖≤K+C/N) :
    ∃ ε : Fin N → ℝ, IsRealSigning ε ∧ ∀ z : ℂ, ‖z‖=1 →
      ‖littlewoodValue ε z‖/Real.sqrt N≤
        K+C/N+196608*(1/Real.sqrt N+2*Real.sqrt (δ*Real.log (20/δ))) := by sorry
