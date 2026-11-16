-- Prove2me | Theorems.Thm_MoneyBurningSurplus_Harmonic_Supplement_lemma_1
-- name    : MoneyBurningSurplus.Harmonic.Supplement.lemma_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T19:57:15.901112+00:00
-- url     : https://prove2.me/theorems/11f3a05d-8a3e-44d1-93c6-cff74a9d5f65
-- title:
--   Lemma 1 — for q ∈ [0,1), M_q is BIC, EPIR, has nonnegative payments and S(q) ≥ U(q)/g_n(q)
-- statement:
--   Let $n\ge2$ agents have finite type sets $T_i$ of nonnegative valuations on a nonempty finite outcome set $O$, with a product prior $D=\prod_iD_i$ giving every type positive mass $f_i(a)>0$. Let $A$ be any allocation algorithm, mapping every report profile to a distribution on $O$, with interim values $G_i(a,b)$ as in (6). Fix a rule $\mathrm{sel}_i(a)\in\arg\max_bG_i(a,b)$, and an admissible LP choice: for every $q\in(0,1)$ and every agent, a row-saturated optimum $x_i^q$ of the assignment LP (7) and an optimum $(u_i^q,\pi_i^q)$ of its dual (8), together with the level-zero convention $\pi_i^0=0$, $u_i^0(a)=\max_bG_i(a,b)$. Let $M_q$ be the fixed-level mechanism of steps 2–4 of the Bayesian harmonic-sampling mechanism, and let
--
--   $$U(q)=\sum_i\sum_{a\in T_i}f_i(a)u_i^q(a),\qquad g_n(q)=\sum_{k=0}^{n-1}(1-q)^k.$$
--
--   Then for every $q\in[0,1)$:
--
--   1. $M_q$ is Bayesian incentive compatible: for every agent $i$ and types $a,b\in T_i$, the interim expected utility $\mathbb E_{v_{-i}\sim D_{-i}}\mathbb E[a(o)-p_i]$ of true type $a$ is at least as large reporting $a$ as reporting $b$;
--   2. $M_q$ is ex-post individually rational: at truthful reports, every realization of positive probability gives every agent $v_i(o)-p_i\ge0$;
--   3. every such realization charges nonnegative payments;
--   4. the expected residual surplus $S(q)$ of $M_q$ under truthful reports $v\sim D$ satisfies
--   $$S(q)\ge\frac{U(q)}{g_n(q)}.\tag{15}$$
--
--   This fixed-level bound is what both the discretized and the continuous versions of Theorem 3 average over the participation level.
--
--   **Formalization Note** A realization of $M_q$ is a triple (set of agents, surrogate profile, outcome); at $q=0$ the set is the singleton of the chosen agent. All expectations are finite sums over these triples and over the prior. The LP choice is a fixed family of functions of the level; the statement holds for every admissible family, and Theorem 3 asserts that such families exist.
--
--   Differences from the source:
--   - encoding: agents N = {1,…,n} with n ≥ 2, nonnegative valuations on a nonempty finite outcome set O → Fin n with 2 ≤ n, real-valued functions O → ℝ with pointwise nonnegativity carried by the domain, Fintype O, Nonempty O, DecidableEq O; reason: relabeling and decidable finite membership change no instance
--   - generalization: type sets T_i whose elements are valuations → finite types Ty i with a valuation map val i (not required to be injective) and masses f i; reason: the paper's setting is the case of an injective map, and the claims do not use injectivity
--   - encoding: an allocation algorithm A, possibly randomized, A^r(v) with fresh randomness r → its outcome distribution A(v), a probability vector on O at every report profile; reason: the mechanism and all four claims depend on A only through these distributions
--   - encoding: choose an optimum x_i^q with every row saturated and an optimal dual (u_i^q, π_i^q), report-independently; at q = 0, π_i^0 = 0 and u_i^0(a) = max_b G_i(a,b) → universally quantified families x, u, π satisfying IsAdmissibleLPChoice on (0,1) and IsLevelZeroConvention; reason: the lemma holds for whatever choice is fixed; the families take no reports
--   - encoding: the q = 0 surrogate ṽ_I ∈ argmax_b G_I(v_I, b) → a universally quantified fixed rule sel with IsArgmaxRule; reason: any fixed choice from the argmax
--   - encoding: BIC, EPIR over the support, nonnegative payments, and S(q) as an expectation over v ∼ D and the mechanism → IsBIC, IsLotteryEPIR and HasLotteryNonnegPayments on seeds of positive probability, and lotterySurplus, as finite sums; reason: these are §2's and App. C.1's definitions for a finite-support prior and a finite lottery
-- source:
--   Tomer Ezra, Money Burning Mechanism Design: From Welfare to Surplus, STOC 2027 submission #585 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/585.pdf, Lemma 1 and equation (15), PDF p. 23 (printed p. 22); mechanism steps 1–4 and payment (14), PDF p. 23 (printed p. 22); LP (7), dual (8), level-zero convention, (11) and (12), PDF p. 22 (printed p. 21); proof PDF pp. 23–24 (printed pp. 22–23)

import Mathlib
import Definitions.Def_MoneyBurningSurplus_Harmonic_Supplement_Bayes

namespace MoneyBurningSurplus.Harmonic.Supplement

theorem lemma_1
    {n : ℕ} (hn : 2 ≤ n) {O : Type*} [Fintype O] [Nonempty O] [DecidableEq O]
    {Ty : Fin n → Type*} [∀ i, Fintype (Ty i)] [∀ i, DecidableEq (Ty i)]
    (val : (i : Fin n) → Ty i → O → ℝ) (f : (i : Fin n) → Ty i → ℝ)
    (hprior : IsFiniteProductPrior val f)
    (A : ((i : Fin n) → Ty i) → O → ℝ) (hA : IsAllocAlgorithm A)
    (sel : (i : Fin n) → Ty i → Ty i) (hsel : IsArgmaxRule val f A sel)
    (x : ℝ → (i : Fin n) → Ty i → Ty i → ℝ) (u π : ℝ → (i : Fin n) → Ty i → ℝ)
    (hLP : IsAdmissibleLPChoice val f A x u π) (h0 : IsLevelZeroConvention val f A u π)
    (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q < 1) :
    IsBIC val f (levelProb f A x sel q) levelOut (levelPay val f A π q) ∧
    IsLotteryEPIR val (levelProb f A x sel q) levelOut (levelPay val f A π q) ∧
    HasLotteryNonnegPayments (levelProb f A x sel q) (levelPay val f A π q) ∧
    dualUtility f u q / gNorm n q ≤
      lotterySurplus val f (levelProb f A x sel q) levelOut (levelPay val f A π q) := by sorry

end MoneyBurningSurplus.Harmonic.Supplement
