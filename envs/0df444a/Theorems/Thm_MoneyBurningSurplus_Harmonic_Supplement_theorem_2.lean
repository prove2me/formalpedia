-- Prove2me | Theorems.Thm_MoneyBurningSurplus_Harmonic_Supplement_theorem_2
-- name    : MoneyBurningSurplus.Harmonic.Supplement.theorem_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T19:56:42.4105+00:00
-- url     : https://prove2.me/theorems/f6ca2c80-49da-44fc-a6e9-29cf7c809e7d
-- title:
--   Theorem 2 — random rescaling turns a UT, EPIR α-approximation for welfare into E[RS] ≥ W(N)/(12α(L+1)), L = ⌈log₂(6αn)⌉
-- statement:
--   Let $n\ge2$ agents have valuations in domains $V_i$ of nonnegative valuations on a nonempty finite outcome set $O$, each closed under multiplication by every real $s>0$. Let $1\le\alpha\le n$. Let $M$ be a randomized mechanism with seed $r\sim\mu$ that is universally truthful, ex-post individually rational and has nonnegative payments on these domains, and is an $\alpha$-approximation for welfare: for every admissible profile $v$,
--
--   $$\mathbb E_r\Big[\sum_{i}v_i\big(o^r(v)\big)\Big]\ge\frac{W(N)}{\alpha},\qquad W(N)=\max_{o\in O}\sum_iv_i(o).$$
--
--   Let $\widetilde M$ be the random-rescaling mechanism with $L=\lceil\log_2(6\alpha n)\rceil$, $\rho=1+1/L$: independent levels $K_i$ with $\Pr[K_i=k]=2^{-(k+1)}$ for $k<L$ and $2^{-L}$ for $k=L$, scales $s_i=\rho^{K_i}$, one run of $M$ on $(s_iv_i)_i$, and payments $p_i/s_i$. Then
--
--   1. $\widetilde M$ is universally truthful (every pair of a scaling vector and a seed of $M$ gives a truthful deterministic mechanism);
--   2. $\widetilde M$ is ex-post individually rational and has nonnegative payments, for every such pair;
--   3. for every admissible profile $v$,
--   $$\mathbb E\Big[\sum_i\big(v_i(o)-\tilde p_i\big)\Big]\ge\frac{W(N)}{12\alpha(L+1)};$$
--   4. $L\le\lceil\log_2(6n^2)\rceil$, so the surplus approximation factor $12\alpha(L+1)$ is $O(\alpha\log n)$.
--
--   This is the paper's black-box reduction from welfare to residual surplus; the constant is the one its proof establishes, and the last clause is the step from it to the printed $O(\alpha\log n)$.
--
--   **Formalization Note** The expectation in 3 is a finite sum over level vectors $K$ of the Bochner integral over $r\sim\mu$. Measurability of $M$ in its seed at admissible profiles is assumed so that expectations are defined; with finitely many outcomes this makes every integrand bounded and integrable. The sentence on invoking $M$ once and computational efficiency has no cost model in the paper and is not a Lean clause: the single invocation is the explicit construction.
--
--   Differences from the source:
--   - encoding: agents N = {1,…,n} with n ≥ 2, nonnegative valuations on a nonempty finite outcome set O → Fin n with 2 ≤ n, real-valued functions O → ℝ with pointwise nonnegativity carried by the domain, Fintype O, Nonempty O, DecidableEq O; reason: relabeling and decidable finite membership change no instance
--   - encoding: a randomized mechanism with internal random seed r drawn independently of the reports → a seed-indexed family (o^r, p^r) on a measurable space with a probability measure μ, measurable in r at admissible profiles; reason: the expectations of §2 require measurability; it excludes no mechanism with finitely many outcomes whose randomness is a random variable
--   - encoding: UT, EPIR and nonnegative payments of M and of the converted mechanism (EPIR and payments for every (o,p) in the support) → AGT.MechIncentiveCompatible, AGT.IndividuallyRational and AGT.NoPositiveTransfers for every seed; reason: §2 defines UT seedwise, and the proof (PDF 10–11) uses and proves EPIR and nonnegative payments seedwise
--   - encoding: scalable valuation domains of valuations O → ℝ≥0 → IsScalableDomain V: every member pointwise nonnegative, s • u ∈ V i for every real s > 0; reason: this is the definition on PDF 8; all reports and deviations lie in V
--   - reading: can be converted into a mechanism with the same properties and surplus approximation factor O(α log n) → the explicit random-rescaling mechanism of PDF 10 is UT, EPIR, has nonnegative payments and E[RS] ≥ W(N)/(12α(L+1)), and L ≤ ⌈log₂(6n²)⌉; reason: the theorem refers to that construction; the explicit constant is the proof's (PDF 12) and implies the printed O(α log n); "the same properties" are the three the proof establishes
--   - reading: the reduction invokes the starting mechanism once and preserves computational efficiency whenever scaled valuations can be accessed efficiently → no Lean clause; the construction calls M once on the scaled profile; reason: the paper gives no cost model for efficiency, and the single call is visible in the definition of M̃
-- source:
--   Tomer Ezra, Money Burning Mechanism Design: From Welfare to Surplus, STOC 2027 submission #585 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/585.pdf, Theorem 2, PDF p. 10 (printed p. 9); construction of M̃, PDF p. 10 (printed p. 9); proof PDF pp. 10–12 (printed pp. 9–11), final bound W(N)/(12α(L+1)) and L ≤ ⌈log₂(6n²)⌉ on PDF p. 12 (printed p. 11)

import Mathlib
import Definitions.Def_MoneyBurningSurplus_Harmonic_Model
import Definitions.Def_MoneyBurningSurplus_Harmonic_Supplement_Rescaling

namespace MoneyBurningSurplus.Harmonic.Supplement

open MeasureTheory

theorem theorem_2
    {n : ℕ} (hn : 2 ≤ n) {O : Type*} [Fintype O] [Nonempty O] [DecidableEq O]
    (α : ℝ) (hα1 : 1 ≤ α) (hαn : α ≤ (n : ℝ))
    (V : Fin n → Set (O → ℝ)) (hV : IsScalableDomain V)
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (M : SeededMech n O Ω) (hmeas : IsSeedMeasurable V M)
    (hUT : IsUniversallyTruthful V M) (hIR : IsExPostIR V M) (hNN : HasNonnegPayments V M)
    (hwel : ∀ v : Fin n → O → ℝ, AGT.IsValProfile V v →
      welfare v Finset.univ / α ≤ expectedWelfare μ M v) :
    IsUniversallyTruthful V (rescaledMech M (rescaleLevels n α)) ∧
    IsExPostIR V (rescaledMech M (rescaleLevels n α)) ∧
    HasNonnegPayments V (rescaledMech M (rescaleLevels n α)) ∧
    (∀ v : Fin n → O → ℝ, AGT.IsValProfile V v →
      welfare v Finset.univ / (12 * α * ((rescaleLevels n α : ℝ) + 1)) ≤
        rescaledSurplus μ M (rescaleLevels n α) v) ∧
    rescaleLevels n α ≤ ⌈Real.logb 2 (6 * (n : ℝ) ^ 2)⌉₊ := by sorry

end MoneyBurningSurplus.Harmonic.Supplement
