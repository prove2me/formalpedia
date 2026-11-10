-- Prove2me | Theorems.Thm_LemonsPoA_TwoSided_theorem_5_1
-- name    : LemonsPoA.TwoSided.theorem_5_1
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T02:12:19.751481+00:00
-- url     : https://prove2.me/theorems/167b1fb2-ea14-47f3-81e7-d6a36928fbb4
-- title:
--   Theorem 5.1 — two-sided reduction: $W^-_S(I)\ge\frac{\Pr[\Sigma_S=\sigma^-_S,\Sigma_B=\sigma^+_B]}{e}\cdot\frac{R}{FB}$
-- statement:
--   Let $I=(v,G,F,\Sigma_S,\Sigma_B)$ be a market instance (affine values $v(c,\theta)=c\,x(\theta)+y(\theta)$, $x\ge 0$, finite signal spaces, the news ordering). Suppose $E[|C|]<\infty$, $FB>0$, and under $G$ the variables $x(\theta),y(\theta)$ have finite first moments and a jointly log-concave density. Let $\sigma^-_S,\sigma^+_B$ be the most pessimistic seller and most optimistic buyer signals (41), $d=m(\sigma^-_S,\sigma^+_B)$ and $R=E[(\hat v_B-\hat v_S)_+]$ with $\hat v=d\,x+y$ (42)-(43). Then the worst-case equilibrium fraction of first-best in the fine-menu limit (25) satisfies
--   $$W^-_S(I)\ \ge\ \frac{\Pr[\Sigma_S=\sigma^-_S,\Sigma_B=\sigma^+_B]}{e}\cdot\frac{R}{FB}.$$
--
--   This reduces the equilibrium analysis to the first-best $R$ of an independent-private-values market.
--
--   Differences from the source:
--   - encoding: joint law of $(C,\Sigma_S,\Sigma_B)$ on $\mathbb R\times S_S\times S_B$, independent of the i.i.d. types $\theta_S,\theta_B\sim G$ → finite measures $F(\sigma_S,\sigma_B)(A)=\Pr[C\in A,\Sigma_S=\sigma_S,\Sigma_B=\sigma_B]$ of total mass $1$; expectations against $F(\sigma_S,\sigma_B)\otimes G\otimes G$ summed over signal pairs; reason: every law on $\mathbb R\times S_S\times S_B$ with finite $S_S,S_B$ is uniquely of this form; same instances
--   - reading: conditional probabilities, $m(\sigma_S,\sigma_B)$, the news ordering (13)-(14), equilibrium conditions 1-4 and Definition 5.2 items 2-3 for all signals → only for signals (and signal pairs) of positive probability; reason: these quantities are undefined on null events; Definition 1.4 writes $\sigma_B\in\mathrm{supp}\,\Sigma_B$
--   - reading: $\sigma^-_S\in\arg\min m(\cdot,\sigma^*_B)$, $\sigma^+_B\in\arg\max m(\sigma^*_S,\cdot)$ simultaneously for all partner signals (41) → universally quantified $\sigma^-_S,\sigma^+_B$ with hypotheses `IsPessimistic`, `IsOptimistic` (extremal among pairs of positive probability); reason: the statement then holds for every admissible choice, ties included, which covers the paper's fixed choice
--   - reading: (21): off-path beliefs are limits along trembles $\ell^n$, "for all $\sigma_P$, $\sigma_R$, and $q$" → one tremble sequence $\ell^n$ (strictly positive, summing to 1 over $Q\cup\{\bot\}$, converging to $\ell$) serves every off-path $(\sigma_B,q)$; reason: Kreps-Wilson consistency, which the paper cites; the stronger requirement on the equilibrium
--   - encoding: $W^-_S(I,Q)=\inf_{E_S(I,Q)}W_S$ and $W^-_S(I)=\inf_{\text{fine}}\liminf_n W^-_S(I,Q_n)$ → infimum and liminf in `EReal` ($\inf\emptyset=+\infty$); reason: the paper's extended-real infimum; avoids the real `sInf ∅ = 0`
--   - encoding: finite menu $Q\subset\mathbb R$, $\mathcal Q=Q\cup\{\bot\}$, strategies of a continuous type space → `Q : Finset ℝ`, exit as `Option.none`, strategies and acceptance probabilities measurable in $\theta$ and $\mathbb R$-valued in $[0,1]$; reason: Lean conventions; measurability is the standing convention that makes the expectations in (16)-(22) defined
-- source:
--   Durvasula, Roughgarden, The Price of Anarchy in Markets for Lemons, STOC 2027 submission (manuscript sha256 5a158b50…), p. 26, Theorem 5.1

import Mathlib
import Definitions.Def_LemonsPoA_TwoSided_Market
import Definitions.Def_LemonsPoA_TwoSided_Game
import Definitions.Def_LemonsPoA_TwoSided_Distributions

open MeasureTheory

namespace LemonsPoA.TwoSided

/-- Theorem 5.1 (p. 26): two-sided reduction to the belief-robust IPV market,
`W⁻_S(I) ≥ (Pr[Σ_S = σ⁻_S, Σ_B = σ⁺_B] / e) · (R / FB)`. -/
theorem theorem_5_1 {Θ : Type*} [MeasurableSpace Θ] {SS SB : Type*} [Fintype SS] [Fintype SB]
    (M : Market Θ SS SB) (hC : Integrable id M.lawC) (hFB : 0 < M.FB)
    (hx : Integrable M.x M.G) (hy : Integrable M.y M.G)
    (hlc : HasLogConcaveJointDensity M.G M.x M.y) (hnews : M.NewsOrdered)
    (σm : SS) (σp : SB) (hσm : M.IsPessimistic σm) (hσp : M.IsOptimistic σp) :
    (((M.jointProb σm σp / Real.exp 1) * (M.R (M.m σm σp) / M.FB) : ℝ) : EReal) ≤ M.Wminus := by sorry

end LemonsPoA.TwoSided
