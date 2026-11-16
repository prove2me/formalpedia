-- Prove2me | Theorems.Thm_MoneyBurningSurplus_Harmonic_Supplement_theorem_3
-- name    : MoneyBurningSurplus.Harmonic.Supplement.theorem_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T19:57:49.8757+00:00
-- url     : https://prove2.me/theorems/75978fbb-2023-47eb-8f94-7ff2589418cd
-- title:
--   Theorem 3 — Bayesian harmonic sampling: M_{D,ε} is BIC, EPIR, nonnegative-payment with E[RS] ≥ SW_A/(H_n+ε); the continuous version achieves SW_A/H_n
-- statement:
--   Let $n\ge2$ agents have finite type sets $T_i$ of nonnegative valuations on a nonempty finite outcome set $O$, with a product prior $D=\prod_iD_i$ giving every type positive mass. Let $A$ be any allocation algorithm (possibly randomized, not necessarily truthful), mapping every report profile to a distribution on $O$, with welfare $SW_A=\mathbb E_{v\sim D}\big[\sum_iv_i(A(v))\big]$ and interim values $G_i$ as in (6). Fix a rule $\mathrm{sel}_i(a)\in\arg\max_bG_i(a,b)$. Then:
--
--   1. **Finite construction.** For every $\varepsilon>0$ and every admissible LP choice (row-saturated optima of (7) and optima of (8) at every level $q\in(0,1)$), the mechanism $M_{D,\varepsilon}$ — $L=\lceil n/\varepsilon\rceil$, $q_j=j/L$, level $J=j$ with probability $g_n(q_j)/(LC_{n,L})$, $C_{n,L}=\frac1L\sum_{j<L}g_n(q_j)$, then $M_{q_J}$ — is Bayesian incentive compatible, ex-post individually rational, has nonnegative payments, and
--   $$\mathbb E_{v\sim D,\,(o,p)\sim M_{D,\varepsilon}(v)}\Big[\sum_{i}\big(v_i(o)-p_i\big)\Big]\ge\frac{SW_A}{H_n+\varepsilon}.$$
--   2. **Continuous version.** For every admissible LP choice that is measurable in the level, the mechanism that draws $q\in(0,1)$ with density $g_n(q)/H_n$ and runs $M_q$ is Bayesian incentive compatible (in interim expected utility, averaged over $q$), every $M_q$ in it is ex-post individually rational with nonnegative payments, and
--   $$\int_0^1\frac{g_n(q)}{H_n}\,S(q)\,dq\ge\frac{SW_A}{H_n}.$$
--   3. Admissible LP choices that are measurable in the level exist.
--
--   The theorem converts any welfare algorithm into a Bayesian mechanism whose residual surplus is within a harmonic factor of the algorithm's welfare, without assuming the algorithm is truthful.
--
--   **Formalization Note** All expectations over the prior and the internal randomness of $M_q$ are finite sums; the continuous version integrates over $q\in(0,1)$ with Lebesgue measure. The level-$0$ component of $M_{D,\varepsilon}$ uses the argmax rule and charges nothing, so it needs no LP data. The sentences on exact interim-value access, invoking $A$ once, and expected polynomial running time have no cost model in the paper and are not Lean clauses.
--
--   Differences from the source:
--   - encoding: agents N = {1,…,n} with n ≥ 2, nonnegative valuations on a nonempty finite outcome set O → Fin n with 2 ≤ n, real-valued functions O → ℝ with pointwise nonnegativity carried by the domain, Fintype O, Nonempty O, DecidableEq O; reason: relabeling and decidable finite membership change no instance
--   - generalization: type sets T_i whose elements are valuations → finite types Ty i with a valuation map val i (not required to be injective) and masses f i; reason: the paper's setting is the case of an injective map, and the claims do not use injectivity
--   - encoding: an allocation algorithm A, possibly randomized, with interim values G_i → its outcome distribution A(v), a probability vector on O at every report profile, with G_i computed exactly by (6); reason: the mechanism and all claims depend on A only through these distributions
--   - reading: there is a BIC, EPIR mechanism M_{D,ε} with nonnegative payments satisfying the bound → the explicit M_{D,ε} of PDF 23 has these properties for every admissible LP choice and every fixed argmax rule; reason: the theorem names that construction; the paper fixes an arbitrary such choice
--   - generalization: a continuous version achieves SW_A/H_n (LP optima chosen by fixed optimal-basis tie-breaking and a fixed row-completion rule, PDF 25) → for every admissible LP choice measurable in q: BIC averaged over q, EPIR and nonnegative payments at every level, and ∫ (g_n/H_n) S(q) dq ≥ SW_A/H_n; plus existence of such a measurable choice; reason: the paper's fixed rule is one such choice; the incentive clauses are those the paper gives every M_q and the finite mixture
--   - reading: given exact interim-value access; invokes A once; expected polynomial overhead under rational encodings → no Lean clause; the interim values are defined exactly and the construction calls A once; reason: the paper gives no cost model for these sentences
--   - encoding: BIC, EPIR over the support, nonnegative payments, expectations over v ∼ D and the mechanism → IsBIC, IsLotteryEPIR, HasLotteryNonnegPayments on seeds of positive probability, lotterySurplus, as finite sums; reason: these are §2's and App. C.1's definitions for a finite-support prior and a finite lottery
-- source:
--   Tomer Ezra, Money Burning Mechanism Design: From Welfare to Surplus, STOC 2027 submission #585 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/585.pdf, Theorem 3, PDF p. 21 (printed p. 20); construction of M_{D,ε} and (13)–(14), PDF p. 23 (printed p. 22); LP (7)–(8), PDF p. 22 (printed p. 21); finite guarantee (16)–(17), PDF p. 24 (printed p. 23); continuous version (18)–(20), PDF pp. 24–25 (printed pp. 23–24)

import Mathlib
import Definitions.Def_MoneyBurningSurplus_Harmonic_Supplement_Bayes

namespace MoneyBurningSurplus.Harmonic.Supplement

open MeasureTheory

theorem theorem_3
    {n : ℕ} (hn : 2 ≤ n) {O : Type*} [Fintype O] [Nonempty O] [DecidableEq O]
    {Ty : Fin n → Type*} [∀ i, Fintype (Ty i)] [∀ i, DecidableEq (Ty i)]
    (val : (i : Fin n) → Ty i → O → ℝ) (f : (i : Fin n) → Ty i → ℝ)
    (hprior : IsFiniteProductPrior val f)
    (A : ((i : Fin n) → Ty i) → O → ℝ) (hA : IsAllocAlgorithm A)
    (sel : (i : Fin n) → Ty i → Ty i) (hsel : IsArgmaxRule val f A sel) :
    -- (a), (b): the finite construction `M_{D,ε}`
    (∀ ε : ℝ, 0 < ε →
      ∀ (x : ℝ → (i : Fin n) → Ty i → Ty i → ℝ) (u π : ℝ → (i : Fin n) → Ty i → ℝ),
        IsAdmissibleLPChoice val f A x u π →
        IsBIC val f (mixtureProb f A x sel ε) (mixtureOut ε) (mixturePay val f A π ε) ∧
        IsLotteryEPIR val (mixtureProb f A x sel ε) (mixtureOut ε) (mixturePay val f A π ε) ∧
        HasLotteryNonnegPayments (mixtureProb f A x sel ε) (mixturePay val f A π ε) ∧
        expectedWelfareA val f A / ((harmonic n : ℝ) + ε) ≤
          lotterySurplus val f (mixtureProb f A x sel ε) (mixtureOut ε)
            (mixturePay val f A π ε)) ∧
    -- (c): the continuous version, `q ∈ (0,1)` with density `g_n(q) / H_n`, then `M_q`
    (∀ (x : ℝ → (i : Fin n) → Ty i → Ty i → ℝ) (u π : ℝ → (i : Fin n) → Ty i → ℝ),
        IsAdmissibleLPChoice val f A x u π →
        (∀ i (a b : Ty i), Measurable (fun q => x q i a b)) →
        (∀ i (b : Ty i), Measurable (fun q => π q i b)) →
        (∀ i (a b : Ty i),
          ∫ q in Set.Ioo (0 : ℝ) 1, gNorm n q / (harmonic n : ℝ) *
              lotteryInterimUtility val f (levelProb f A x sel q) levelOut
                (levelPay val f A π q) i a b ≤
            ∫ q in Set.Ioo (0 : ℝ) 1, gNorm n q / (harmonic n : ℝ) *
              lotteryInterimUtility val f (levelProb f A x sel q) levelOut
                (levelPay val f A π q) i a a) ∧
        (∀ q ∈ Set.Ioo (0 : ℝ) 1,
          IsLotteryEPIR val (levelProb f A x sel q) levelOut (levelPay val f A π q) ∧
          HasLotteryNonnegPayments (levelProb f A x sel q) (levelPay val f A π q)) ∧
        expectedWelfareA val f A / (harmonic n : ℝ) ≤
          ∫ q in Set.Ioo (0 : ℝ) 1, gNorm n q / (harmonic n : ℝ) *
            lotterySurplus val f (levelProb f A x sel q) levelOut (levelPay val f A π q)) ∧
    -- admissible LP choices exist, measurably in the level
    (∃ (x : ℝ → (i : Fin n) → Ty i → Ty i → ℝ) (u π : ℝ → (i : Fin n) → Ty i → ℝ),
        IsAdmissibleLPChoice val f A x u π ∧
        (∀ i (a b : Ty i), Measurable (fun q => x q i a b)) ∧
        (∀ i (b : Ty i), Measurable (fun q => π q i b))) := by sorry

end MoneyBurningSurplus.Harmonic.Supplement
