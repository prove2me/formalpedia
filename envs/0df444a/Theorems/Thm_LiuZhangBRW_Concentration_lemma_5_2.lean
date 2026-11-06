-- Prove2me | Theorems.Thm_LiuZhangBRW_Concentration_lemma_5_2
-- name    : LiuZhangBRW.Concentration.lemma_5_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-05T20:19:51.03174+00:00
-- url     : https://prove2.me/theorems/6a80e9ea-deea-4beb-be00-2c9a92e33aac
-- title:
--   Lemma 5.2 (L-Lipschitz) — $|\mathbb E_iX_\ell-\mathbb E_{i-1}X_\ell|\le L|X_i|/N+L\,\mathbb E_{i-1}|X_i|/N$
-- statement:
--   Let $1\le i<\ell$, let $X_1,\dots,X_i$ be measurable and $X_i,X_\ell$ integrable, $L\ge0$ and $N\ge1$. Suppose the L-Lipschitz condition
--   $$
--   \bigl|\mathbb E_{i-1}(X_\ell\mid X_i)-\mathbb E_{i-1}(X_\ell\mid X_i')\bigr|\le L\,\frac{|X_i-X_i'|}{N}\tag{5.5}
--   $$
--   holds, where $X_i'$ is a conditionally independent copy of $X_i$ given $(X_1,\dots,X_{i-1})$. Then almost surely
--   $$
--   \bigl|\mathbb E_i(X_\ell)-\mathbb E_{i-1}(X_\ell)\bigr|\le L\,\frac{|X_i|}{N}+L\,\frac{\mathbb E_{i-1}(|X_i|)}{N}.\tag{5.6}
--   $$
--
--   The lemma turns the Lipschitz condition into a bound on each drift term of (5.4), linear in $|X_i|$ and its conditional mean.
--
--   **Formalization Note** (5.5) is `IsLipschitzInIncrement μ X i ℓ (L / N)`, with $\mathbb E_i$ the conditional expectation given $\sigma(X_1,\dots,X_i)$.
--
--   Differences from the source:
--   - reading: (5.5)/(5.7)/(6.9) with X′_i a conditionally independent copy of X_i given X_1, ..., X_{i−1} → IsLipschitzInIncrement: a version g of E_i X_ℓ as a function of (past, X_i) satisfies |g(p,x) − g(p,x′)| ≤ (L/N)|x − x′| for almost every past p and almost every pair (x, x′) drawn from the product of the conditional law of X_i given p with itself; reason: this is how the proof of Lemma 5.2 (pp. 9–10) uses the condition; demanding the bound for every x, x′ of one version would be a stronger hypothesis
--   - reading: L a Lipschitz constant, N 'a constant integer' that divides (p. 6) → L ≥ 0 and N ≥ 1; reason: implicit on the page; with L < 0 Lemma 5.2 fails for a deterministic X_i ≡ 1
--   - encoding: X_i, X_ℓ random variables, X_1, ..., X_{i−1} the conditioning variables → X_1, ..., X_i measurable, X_i and X_ℓ integrable; reason: the conditional expectations in (5.5)–(5.6) are defined only for integrable variables
--   - encoding: (5.6) as an inequality of random variables → almost surely; reason: conditional expectations are defined up to null sets
-- source:
--   Liu, Zhang, Concentration Inequalities for Branching Random Walks with Applications to Phase Transitions in CSPs, arXiv:1601.04794 (artifact sha256 7499631b9d550f66e791c0b3df0879f26102f111fee3052e363ebbff0c72bdcb; no version stamp), Lemma 5.2, (5.5)–(5.6), p. 9

import Mathlib
import Definitions.Def_LiuZhangBRW_Concentration_natF
import Definitions.Def_LiuZhangBRW_Concentration_IsLipschitzInIncrement

open MeasureTheory

namespace LiuZhangBRW.Concentration

/-- Lemma 5.2 (L-Lipschitz) (Liu, Zhang, *Concentration Inequalities for Branching Random Walks with Applications to
Phase Transitions in CSPs*, arXiv:1601.04794, artifact sha256 7499631b…bdcb, p. 9). If
(5.5) `|E_{i−1}(X_ℓ | X_i) − E_{i−1}(X_ℓ | X′_i)| ≤ L|X_i − X′_i|/N` for `i < ℓ`, then
(5.6) `|E_i(X_ℓ) − E_{i−1}(X_ℓ)| ≤ L|X_i|/N + L E_{i−1}(|X_i|)/N` almost surely.

**Formalization Note** (5.5) is `IsLipschitzInIncrement μ X i ℓ (L / N)` (the conditionally
independent copy, almost surely). Fixed indices `1 ≤ i < ℓ`. `X_1, …, X_i` are measurable,
`X_i` and `X_ℓ` integrable (so the conditional expectations are defined), `L ≥ 0` (a
Lipschitz constant; with `L < 0` the claim fails for a deterministic `X_i ≡ 1`), and `N ≥ 1`
(the integer of §4.2, p. 6). `E_i = condExp (natF X i) μ`. -/
theorem lemma_5_2 {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : ℕ → Ω → ℝ) (i ℓ : ℕ) (hi : 1 ≤ i) (hiℓ : i < ℓ)
    (hmeas : ∀ j ∈ Finset.Icc 1 i, Measurable (X j))
    (hXi : Integrable (X i) μ) (hXℓ : Integrable (X ℓ) μ) (L : ℝ) (N : ℕ) (hL : 0 ≤ L)
    (hN : 1 ≤ N) (hLip : IsLipschitzInIncrement μ X i ℓ (L / N)) :
    ∀ᵐ ω ∂μ, |condExp (natF X i) μ (X ℓ) ω - condExp (natF X (i - 1)) μ (X ℓ) ω| ≤
      L * |X i ω| / N + L * condExp (natF X (i - 1)) μ (fun ω' => |X i ω'|) ω / N := by sorry

end LiuZhangBRW.Concentration
