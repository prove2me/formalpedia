-- Prove2me | Theorems.Thm_OAI_RandomKSAT_sentinel_linear_lower
-- name    : OAI.RandomKSAT.sentinel_linear_lower
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T18:36:47.555686+00:00
-- url     : https://prove2.me/theorems/ab9a5fee-f661-4945-8e61-66564e68a68b
-- title:
--   Linear lower bound for the variance of the satisfiability stopping time of $2Rn$ random $k$-clauses
-- statement:
--   Fix natural numbers $n,k,R$. A $k$-clause on the Boolean variables $x_1,\dots,x_n$ is a pair $(S,\sigma)$ consisting of a set $S\subseteq\{1,\dots,n\}$ of exactly $k$ variables and a sign pattern $\sigma\colon S\to\{0,1\}$; an assignment $x\in\{0,1\}^n$ satisfies $(S,\sigma)$ if $x_v=\sigma(v)$ for at least one $v\in S$. Let $\mathcal C_{n,k}$ denote the finite set of all $k$-clauses on $n$ variables.
--
--   Put $M=2Rn$. For a word $w=(w_1,\dots,w_M)\in\mathcal C_{n,k}^{M}$ define its stopping time with sentinel value $M+1$ by
--
--   $$
--   \tau(w)=\min\bigl\{m\in\{0,1,\dots,M\} : w_1,\dots,w_m \text{ have no common satisfying assignment}\bigr\},
--   $$
--
--   with the convention $\tau(w)=M+1$ when all $M$ clauses are simultaneously satisfiable. Since the empty prefix is satisfiable, $\tau(w)\in\{1,\dots,M+1\}$. Let $\operatorname{Var}(\tau)$ be the variance of $\tau(w)$ when $w$ is drawn uniformly from $\mathcal C_{n,k}^{M}$ (equivalently, $w_1,\dots,w_M$ are independent uniform clauses):
--
--   $$
--   \operatorname{Var}(\tau)=\frac{1}{|\mathcal C_{n,k}|^{M}}\sum_{w}\tau(w)^2-\Bigl(\frac{1}{|\mathcal C_{n,k}|^{M}}\sum_{w}\tau(w)\Bigr)^2 .
--   $$
--
--   **Theorem.** Assume that $2\le k\le n$, $R\ge 1$ and $n\ge 2k^2$, and let $a$ be a real number such that
--
--   1. $0<a\le 1$ and $e^{2}a\le \tfrac12$;
--   2. $2a\le \tfrac14 e^{-4Rk^2}$ and $an\ge 8$;
--   3. $\bigl(2(1-2^{-k})^{R}\bigr)^{n}\le \tfrac14 e^{-4Rk^2}$.
--
--   Then, with $M=2Rn$,
--
--   $$
--   \frac{a}{16(2R+1)^2}\cdot a\cdot e^{-4Rk^2}\cdot\frac{n}{16}\;\le\;\operatorname{Var}(\tau),
--   $$
--
--   that is, $\operatorname{Var}(\tau)\ge a^2e^{-4Rk^2}\,n/\bigl(256(2R+1)^2\bigr)$.
--
--   For fixed $k$ one can choose $R$ with $2(1-2^{-k})^R<1$ and then $a>0$ depending only on $k$ and $R$, so that all hypotheses hold for every sufficiently large $n$. The theorem then says that the satisfiability stopping time of $2Rn$ independent random $k$-clauses has variance at least a positive constant (depending only on $k$, $R$ and $a$) times $n$, so its standard deviation is at least of order $\sqrt n$. This is the combinatorial core of the linear lower bounds for the variance of the (capped and uncapped) first unsatisfiability time of random $k$-SAT.
--
--   **Formalization Note** The variance is the elementary `fvariance` of a real function on the finite type `Fin (2*R*n) → Clause n k` (uniform average of the square minus the square of the uniform average), and $\tau$ is `listStop (List.ofFn w)`, defined as the least $m$ such that $m$ equals the length plus one or the first $m$ clauses are not simultaneously satisfiable. Variables are indexed by `Fin n`. The hypothesis `Real.exp 2*a ≤ 1/2` reads $e^2\cdot a\le 1/2$, and the constant $2R+1$ appears as the cast of the natural number `2*R` plus one.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/SATVariance/FailureWindows.lean#L180-L233

import Mathlib
import Definitions.Def_SATVariance
import Definitions.Def_OAI_Probability_SATVariance_ClauseCombinatorics__SATVariance
import Definitions.Def_OAI_Probability_SATVariance_FrozenReplacement__SATVariance
import Definitions.Def_OAI_Probability_SATVariance_BlockKilling
import Definitions.Def_OAI_Probability_SATVariance_MarkovReplacement__SATVariance
import Definitions.Def_OAI_Probability_SATVariance_FiniteVariance
import Definitions.Def_OAI_Probability_SATVariance_LifetimePotential
import Definitions.Def_OAI_Probability_SATVariance_RootDisintegration__SATVariance
import Definitions.Def_OAI_Probability_SATVariance_FiberRefresh
import Definitions.Def_OAI_Probability_SATVariance_PairEvolution
import Definitions.Def_OAI_Probability_SATVariance_HiddenTests
import Definitions.Def_OAI_Probability_SATVariance_WeightedRewards
import Definitions.Def_OAI_Probability_SATVariance_CountMoments
import Definitions.Def_OAI_Probability_SATVariance_SupportProbabilities__SATVariance
import Definitions.Def_OAI_Probability_SATVariance_OmissionCompression
import Definitions.Def_OAI_Probability_SATVariance_CapBridge
import Definitions.Def_OAI_Probability_SATVariance_ShuffleAverages
import Definitions.Def_OAI_Probability_SATVariance_BystanderStops
import Definitions.Def_OAI_Probability_SATVariance_InsertionVariance
import Definitions.Def_OAI_Probability_SATVariance_IsolatedSupports
import Definitions.Def_OAI_Probability_SATVariance_BystanderVariance

open OAI OAI.RandomKSAT
open MeasureTheory ProbabilityTheory
open scoped Classical ENNReal

theorem OAI.RandomKSAT.sentinel_linear_lower {n k R : ℕ} (hk : 2 ≤ k) (hkn : k ≤ n)
    (hR : 1 ≤ R) (hn : 2*k^2 ≤ n) {a : ℝ} (ha : 0 < a) (ha1 : a ≤ 1)
    (haHall : Real.exp 2*a ≤ 1/2) (haβ : 2*a ≤ Real.exp (-4*(R:ℝ)*k^2)/4)
    (hlarge : 8 ≤ a*n)
    (hhigh : (2*(1-((2:ℝ)^k)⁻¹)^R)^n ≤ Real.exp (-4*(R:ℝ)*k^2)/4) :
    (a/(16*((2*R:ℕ)+1:ℝ)^2))*a*Real.exp (-4*(R:ℝ)*k^2)/16*n ≤
      fvariance (fun w : Fin (2*R*n) → Clause n k => (listStop (List.ofFn w):ℝ)) := by sorry
