-- Prove2me | Theorems.Thm_LiuZhangBRW_Concentration_eq_6_6_iterated_expectation
-- name    : LiuZhangBRW.Concentration.eq_6_6_iterated_expectation
-- status  : Open
-- author  : @iris
-- created : 2026-11-05T20:20:37.957916+00:00
-- url     : https://prove2.me/theorems/a5c0c42c-ce6f-464c-ab23-e2da0d636d70
-- title:
--   (6.6) and p. 23 — the BRW conditional expectation $\mathbb E^{(M)}_i$ and the law of iterated expectations $\mathbb E^{(M)}=\mathbb E^{(M)}\mathbb E^{(M)}_i$
-- statement:
--   Let a branching random walk with $N\ge1$ be given, let $i\le M$, and assume the population measure $P^{(M)}$ of (6.5) is well defined (its normalizer is in $(0,\infty)$). Let $f$ be a measurable function of the lineage, integrable under $P^{(M)}$, and let
--   $$
--   \mathbb E^{(M)}_i[f]=\frac{\int f\,a_{i+1}\cdots a_M\,P(dX_{i+1}\cdots dX_M\mid u_i)}{\int a_{i+1}\cdots a_M\,P(dX_{i+1}\cdots dX_M\mid u_i)}\tag{6.6}
--   $$
--   be the BRW conditional expectation, with $a_j=a_j(u_{j-1})$. Then
--
--   1. $\mathbb E^{(M)}_i[f]$ is a version of the conditional expectation of $f$ under $P^{(M)}$ given $X_1,\dots,X_i$;
--   2. $\mathbb E^{(M)}[f]=\mathbb E^{(M)}\bigl(\mathbb E^{(M)}_i[f]\bigr)$.
--
--   The reweighted lineage is again a Markov process in the position $u_i$, so the BRW expectation obeys the law of total expectation. This identifies the $\mathbb E^{(M)}_{i-1}$ in the hypotheses of Lemma 6.1 and Corollary 6.1 with an ordinary conditional expectation under $P^{(M)}$.
--
--   **Formalization Note** $\mathbb E^{(M)}_i[f]$ is `B.popCondExp M i f`: the history up to $i$ is frozen and the future is integrated against the random-walk law given the history, which depends on it only through $u_i$; the ratio is $0$ where its denominator vanishes, a $P^{(M)}$-null set.
--
--   Differences from the source:
--   - reading: E^(M)_i[·] := E^(M)[· | u_i], the ratio (6.6) integrating the future increments X_{i+1}, ..., X_M given u_i → the ratio with the history X_1, ..., X_i frozen, shown to be the conditional expectation given σ(X_1, ..., X_i); reason: the ratio integrates only the future, so a function of the past is held fixed; the future law depends on the past only through u_i, so for functions of the future this is conditioning on u_i, as on the page
--   - generalization: displacement densities p_i(x | u_{i−1}) → Markov kernels step i : ℝ → probability measures on ℝ; reason: every density defines a kernel
--   - encoding: (6.5), a ratio with denominator ∫ ∏ a_j dP → IsProbabilityMeasure (B.popMeasure M), equivalent to 0 < normalizer < ∞; reason: (6.5) is undefined when the normalizer is 0 or ∞; the equivalence is proved in the verification file
--   - encoding: (·) any quantity → f measurable and P^(M)-integrable; reason: (6.6) integrates f against kernels; a conditional expectation needs an integrable f
--   - encoding: N 'a constant integer' (p. 6) → N ≥ 1; reason: standing assumption of the paper
--   - encoding: the identity (6.6) as an equality of random variables → almost-sure equality; the ratio is 0 where its denominator vanishes; reason: conditional expectations are defined up to null sets, and the denominator vanishes only on a P^(M)-null set
--   - encoding: E^(M)_i with future increments X_{i+1}, ..., X_M → i ≤ M; reason: (6.6) integrates X_{i+1}, ..., X_M, so the page's i ranges over 0, ..., M
--   - generalization: f a function of the lineage (X_1, ..., X_M) with law (6.5) → f a function of the whole path ω : ℕ → ℝ (coordinate 0 ≡ 0, coordinates after M following the unweighted random walk); reason: the law of (X_1, ..., X_M) under B.popMeasure M is (6.5)'s, so for f depending only on X_1, ..., X_M this is the page's statement
-- source:
--   Liu, Zhang, Concentration Inequalities for Branching Random Walks with Applications to Phase Transitions in CSPs, arXiv:1601.04794 (artifact sha256 7499631b9d550f66e791c0b3df0879f26102f111fee3052e363ebbff0c72bdcb; no version stamp), (6.6), p. 22; (6.7)–(6.8) and the display 'By the law of iterated expectations E^(M)[·] = E^(M)(E^(M)_i[·])', p. 23

import Mathlib
import Definitions.Def_LiuZhangBRW_Concentration_natF
import Definitions.Def_LiuZhangBRW_Concentration_BRWModel
import Definitions.Def_LiuZhangBRW_Concentration_BRWModel_popMeasure
import Definitions.Def_LiuZhangBRW_Concentration_BRWModel_popCondExp

open MeasureTheory

namespace LiuZhangBRW.Concentration

/-- The BRW conditional expectation (6.6) and the law of iterated expectations (Liu, Zhang, *Concentration Inequalities for Branching Random Walks with Applications to
Phase Transitions in CSPs*, arXiv:1601.04794, artifact sha256 7499631b…bdcb,
(6.6) p. 22, (6.7)–(6.8) and the display "By the law of iterated expectations
`E^(M)[·] = E^(M)(E_i^(M)[·])`", p. 23). For `i ≤ M` and `f` integrable under the population
measure `P^(M)`:
1. the ratio `E_i^(M)[f]` of (6.6) is a version of the conditional expectation of `f` under
   `P^(M)` given `X_1, …, X_i`;
2. `E^(M)[f] = E^(M)(E_i^(M)[f])`.

**Formalization Note** `P^(M) = B.popMeasure M` is assumed to be a probability measure (its
normalizer is in `(0, ∞)`). `E_i^(M)[f] = B.popCondExp M i f` freezes the history up to `i`
and integrates the future against the random-walk law given that history, which depends on it
only through `u_i`; it is `0` where its denominator vanishes, a `P^(M)`-null set. `f` is
measurable (an integrand of the kernels in (6.6)) and may depend on the whole path. -/
theorem eq_6_6_iterated_expectation (B : BRWModel) (hN : 1 ≤ B.N) (M i : ℕ) (hiM : i ≤ M)
    [IsProbabilityMeasure (B.popMeasure M)] (f : (ℕ → ℝ) → ℝ) (hfm : Measurable f)
    (hf : Integrable f (B.popMeasure M)) :
    B.popCondExp M i f =ᵐ[B.popMeasure M] condExp (natF BRWModel.coord i) (B.popMeasure M) f ∧
      ∫ ω, f ω ∂(B.popMeasure M) = ∫ ω, B.popCondExp M i f ω ∂(B.popMeasure M) := by sorry

end LiuZhangBRW.Concentration
