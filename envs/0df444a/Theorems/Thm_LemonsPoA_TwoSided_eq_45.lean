-- Prove2me | Theorems.Thm_LemonsPoA_TwoSided_eq_45
-- name    : LemonsPoA.TwoSided.eq_45
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T02:12:19.753707+00:00
-- url     : https://prove2.me/theorems/4e91602e-fb05-4834-b231-1c20ae386a96
-- title:
--   §5.1, Eq. (45) — every equilibrium has $W_S\cdot FB\ge\Pr[\Sigma_S=\sigma^-_S,\Sigma_B=\sigma^+_B]\,E[u_Q(\hat v_S)]$
-- statement:
--   Let $I$ be a market instance with the news ordering, $E|C|<\infty$ and $x(\theta),y(\theta)$ integrable under $G$; let $\sigma^-_S$ be a most pessimistic seller signal and $\sigma^+_B$ a most optimistic buyer signal (41), $d=m(\sigma^-_S,\sigma^+_B)$, and $\hat v(\theta)=d\,x(\theta)+y(\theta)$ the belief-robust value with $\hat v_S=\hat v(\theta_S)$, $\hat v_B=\hat v(\theta_B)$. Let $u_Q$ be the finite-menu monopoly profit (30) against $\hat v_B$. Then for every finite menu $Q$ and every sequential equilibrium $(p,a,\lambda)$ of the seller-proposer game on $Q$,
--   $$W_S(p,a,\lambda)\,FB\ \ge\ \Pr[\Sigma_S=\sigma^-_S,\Sigma_B=\sigma^+_B]\cdot E[u_Q(\hat v_S)],$$
--   where $W_S(p,a,\lambda)\,FB=E\big[\sum_{q\in Q}p_q(\theta_S,\Sigma_S)a(\theta_B,\Sigma_B,q)(v(C,\theta_B)-v(C,\theta_S))\big]$ is the equilibrium gains from trade (22).
--
--   This is the two-sided deviation bound: a seller with the most pessimistic signal can secure the belief-robust monopoly profit against buyers with the most optimistic signal.
--
--   **Formalization Note** The left side is `M.gain e`, the expectation in (22) without the factor $1/FB$.
--
--   Differences from the source:
--   - encoding: joint law of $(C,\Sigma_S,\Sigma_B)$ on $\mathbb R\times S_S\times S_B$, independent of the i.i.d. types $\theta_S,\theta_B\sim G$ → finite measures $F(\sigma_S,\sigma_B)(A)=\Pr[C\in A,\Sigma_S=\sigma_S,\Sigma_B=\sigma_B]$ of total mass $1$; expectations against $F(\sigma_S,\sigma_B)\otimes G\otimes G$ summed over signal pairs; reason: every law on $\mathbb R\times S_S\times S_B$ with finite $S_S,S_B$ is uniquely of this form; same instances
--   - reading: conditional probabilities, $m(\sigma_S,\sigma_B)$, the news ordering (13)-(14), equilibrium conditions 1-4 and Definition 5.2 items 2-3 for all signals → only for signals (and signal pairs) of positive probability; reason: these quantities are undefined on null events; Definition 1.4 writes $\sigma_B\in\mathrm{supp}\,\Sigma_B$
--   - reading: $\sigma^-_S\in\arg\min m(\cdot,\sigma^*_B)$, $\sigma^+_B\in\arg\max m(\sigma^*_S,\cdot)$ simultaneously for all partner signals (41) → universally quantified $\sigma^-_S,\sigma^+_B$ with hypotheses `IsPessimistic`, `IsOptimistic` (extremal among pairs of positive probability); reason: the statement then holds for every admissible choice, ties included, which covers the paper's fixed choice
--   - reading: (21): off-path beliefs are limits along trembles $\ell^n$, "for all $\sigma_P$, $\sigma_R$, and $q$" → one tremble sequence $\ell^n$ (strictly positive, summing to 1 over $Q\cup\{\bot\}$, converging to $\ell$) serves every off-path $(\sigma_B,q)$; reason: Kreps-Wilson consistency, which the paper cites; the stronger requirement on the equilibrium
--   - encoding: finite menu $Q\subset\mathbb R$, $\mathcal Q=Q\cup\{\bot\}$, strategies of a continuous type space → `Q : Finset ℝ`, exit as `Option.none`, strategies and acceptance probabilities measurable in $\theta$ and $\mathbb R$-valued in $[0,1]$; reason: Lean conventions; measurability is the standing convention that makes the expectations in (16)-(22) defined
--   - generalization: (45) is derived inside the proof of Theorem 5.1, under its hypotheses $E|C|<\infty$, $FB>0$, finite first moments and a jointly log-concave density → hypotheses $E|C|<\infty$, $x,y$ integrable and the news ordering only; reason: the deviation argument (pp. 26-27) uses neither $FB>0$ nor log-concavity; the statement specializes to the paper's context
--   - encoding: $W_S(p,a,\lambda)\,FB$ → `M.gain e`, the expectation in (22); reason: equal when $FB>0$, and defined without dividing by $FB$
-- source:
--   Durvasula, Roughgarden, The Price of Anarchy in Markets for Lemons, STOC 2027 submission (manuscript sha256 5a158b50…), p. 26-27, §5.1, Eq. (45) (in the proof of Theorem 5.1)

import Mathlib
import Definitions.Def_LemonsPoA_TwoSided_Monopoly
import Definitions.Def_LemonsPoA_TwoSided_Market
import Definitions.Def_LemonsPoA_TwoSided_Game

open MeasureTheory

namespace LemonsPoA.TwoSided

/-- §5.1, Eq. (45) (pp. 26–27): every sequential equilibrium on a finite menu `Q` has
`W_S · FB ≥ Pr[Σ_S = σ⁻_S, Σ_B = σ⁺_B] · E[u_Q(v̂_S)]`, with the belief-robust values at
`d = m(σ⁻_S, σ⁺_B)`; `W_S · FB` is the expectation in (22). -/
theorem eq_45 {Θ : Type*} [MeasurableSpace Θ] {SS SB : Type*} [Fintype SS] [Fintype SB]
    (M : Market Θ SS SB) (hC : Integrable id M.lawC) (hx : Integrable M.x M.G)
    (hy : Integrable M.y M.G) (hnews : M.NewsOrdered)
    (σm : SS) (σp : SB) (hσm : M.IsPessimistic σm) (hσp : M.IsOptimistic σp)
    (Q : Finset ℝ) (e : Assessment Θ SS SB Q) (he : M.IsSeqEq e) :
    M.jointProb σm σp *
        ∫ θ, uQ (M.G.map (M.vhat (M.m σm σp))) Q (M.vhat (M.m σm σp) θ) ∂M.G
      ≤ M.gain e := by sorry

end LemonsPoA.TwoSided
