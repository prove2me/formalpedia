-- Prove2me | Theorems.Thm_LightningNetwork_RateBounds_theorem_2_bounds_on_payment_rates
-- name    : LightningNetwork.RateBounds.theorem_2_bounds_on_payment_rates
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-30T00:56:08.040017+00:00
-- url     : https://prove2.me/theorems/3c159887-d807-4589-a2ac-21f61e69c1ea
-- title:
--   Theorem 2: a channel beats on-chain only if $C > \log(1+B\log(1+r/\lambda))$ (unidirectional) or $C > 3(B\kappa^4/4)^{1/3} - \frac{B}{12}\kappa^2$ (symmetric bidirectional), with $o(r)$ expansions
-- statement:
--   **Theorem 2 (Bounds on Payment Rates).** Let $\lambda > 0$ be a payment rate, $r > 0$ the continuously compounded interest rate, $B \ge 0$ the cost of resetting a channel and $C$ the cost of an on-chain transaction. Settling a Poisson stream of rate $\lambda$ on-chain costs $C\lambda/r$ (Lemma 1); a unidirectional channel of size $m$ costs $m + B\bigl(((r+\lambda)/\lambda)^m - 1\bigr)^{-1}$ (Theorem 1(i)); a bidirectional channel with rates $\lambda_1 = \lambda_2 = \lambda$ and commitments $l_1, l_2$ costs $c^{l_1,l_2}(\lambda,\lambda)$ of Theorem 1(ii), eq. (3). Let
--
--   $$
--   \kappa = \log\frac{r + 2\lambda + \sqrt{r(4\lambda + r)}}{2\lambda}.
--   $$
--
--   1. **(i), inequality (5).** If a unidirectional channel of some size $m > 0$ costs strictly less than $C\lambda/r$, then
--   $$
--   C > \log\bigl(1 + B\log(1 + r/\lambda)\bigr).
--   $$
--   2. **(i), expansion (5).** For fixed $\lambda > 0$ and $B \ge 0$, as $r \to 0^+$,
--   $$
--   \log\bigl(1 + B\log(1 + r/\lambda)\bigr) = \frac{Br}{\lambda} + o(r).
--   $$
--   3. **(ii), inequality (6).** If a symmetric bidirectional channel with some commitments $l_1, l_2 > 0$ costs strictly less than the on-chain cost $2C\lambda/r$ of the two streams, then
--   $$
--   C > 3\left(\frac{B\kappa^4}{4}\right)^{1/3} - \frac{B}{12}\kappa^2 .
--   $$
--   4. **(ii), expansion (6).** For fixed $\lambda > 0$ and $B \ge 0$, as $r \to 0^+$,
--   $$
--   3\left(\frac{B\kappa^4}{4}\right)^{1/3} - \frac{B}{12}\kappa^2 = 3\left(\frac{Br^2}{4\lambda^2}\right)^{1/3} - \frac{Br}{12\lambda} + o(r).
--   $$
--
--   The theorem gives necessary conditions for payment channels to be worth opening: on-chain fees must be high relative to reset costs, payment rates must be high, or interest rates low. For small $r$, a unidirectional channel needs $C$ of order $r$, a symmetric bidirectional one only of order $r^{2/3}$.
--
--   **Formalization Note** Each "$= \dots + o(r)$" is a separate little-o statement along $r \to 0^+$ with $\lambda$ and $B$ fixed; cube roots are real powers of nonnegative numbers.
--
--   Differences from the source:
--   - encoding: the cost of a channel (Theorem 1) and of on-chain settlement (Lemma 1) → the closed forms (1), (3)–(4) and Cλ/r, as the definitions uniCost, bidiCost, onChainCost; reason: the proof uses Theorem 1 and Lemma 1 only through these formulas; their stochastic content is not formalized
--   - reading: a channel costs less than on-chain transactions → some commitment (m > 0, resp. l1, l2 > 0) gives a cost strictly below the on-chain cost; reason: the proof's criterion is inf_{m>0}(cost − on-chain) > 0 for suboptimality, and the infimum is attained, so its negation is this existential; it is not a hypothesis on the minimal cost
--   - generalization: channel balances (commitments) in the model → real commitments m, l1, l2 > 0; reason: the paper itself optimizes over real m; an existential over reals is a weaker premise, so the statement implies the case of any restricted set of sizes
--   - generalization: B > 0 and C > 0 (costs of reset and of an on-chain transaction) → B ≥ 0 and C any real number; reason: at B = 0 both bounds are 0 and the conclusions still hold; C ≤ 0 makes the premises false; the statement specializes to B, C > 0
--   - reading: C > X = Y + o(r) → two clauses: X < C, and (X − Y)(r) = o(r) as r → 0⁺ (little-o along 𝓝[>] 0) for fixed λ > 0, B ≥ 0; reason: r is an interest rate and the paper's regime is r near zero (§3.2); both clauses of (5) and of (6) are stated
--   - reading: a bidirectional symmetric channel with rates λ → λ1 = λ2 = λ with arbitrary commitments l1, l2 > 0; reason: symmetric refers to the rates; the reduction to l1 = l2 is a step of the proof, not a hypothesis
-- source:
--   Guasoni, Huberman, Shikhelman, Lightning Network Economics: Channels, Management Science (2023), doi:10.1287/mnsc.2022.01664, Theorem 2, eqs. (5)–(6), pp. 6–7; proof pp. 11–12

import Mathlib
import Definitions.Def_LightningNetwork_RateBounds_uniCost
import Definitions.Def_LightningNetwork_RateBounds_bidiCost
import Definitions.Def_LightningNetwork_RateBounds_onChainCost
import Definitions.Def_LightningNetwork_RateBounds_kappa

open Filter Topology Asymptotics

namespace LightningNetwork.RateBounds

/-- **Theorem 2 (Bounds on Payment Rates).**
Guasoni, Huberman, Shikhelman, *Lightning Network Economics: Channels*, Management Science (2023),
doi:10.1287/mnsc.2022.01664, Theorem 2, eqs. (5)–(6), pp. 6–7:
"(i) If a unidirectional channel with rate λ costs less than on-chain transactions, then
C > log(1 + B log(1 + r/λ)) = Br/λ + o(r). (5)
(ii) If a bidirectional symmetric channel with rates λ costs less than on-chain transactions,
then C > 3(Bκ⁴/4)^{1/3} − (B/12)κ² = 3(Br²/(4λ²))^{1/3} − Br/(12λ) + o(r) (6)
where κ = log((r + 2λ + √(r(4λ + r)))/(2λ))."

Four clauses, for a payment rate `lam > 0`, interest rate `r > 0`, reset cost `B ≥ 0` and any
on-chain cost `C`:
1. (5), inequality: if some unidirectional channel of size `m > 0` costs strictly less than
   on-chain settlement (`uniCost B r lam m < C·lam/r`), then `C > log(1 + B log(1 + r/lam))`;
2. (5), expansion: for fixed `lam > 0`, `B ≥ 0`,
   `log(1 + B log(1 + r/lam)) − Br/lam = o(r)` as `r → 0⁺`;
3. (6), inequality: if some symmetric bidirectional channel (rates `lam` both ways) with
   commitments `l1, l2 > 0` costs strictly less than settling both streams on-chain
   (`bidiCost B r lam lam l1 l2 < 2·C·lam/r`), then `C > 3(Bκ⁴/4)^{1/3} − (B/12)κ²`;
4. (6), expansion: for fixed `lam > 0`, `B ≥ 0`,
   `(3(Bκ⁴/4)^{1/3} − (B/12)κ²) − (3(Br²/(4lam²))^{1/3} − Br/(12 lam)) = o(r)` as `r → 0⁺`.

**Formalization Note.** Channel costs are Theorem 1's closed forms (1), (3)–(4) and the
on-chain cost is Lemma 1's `Cλ/r` (for two streams, `2Cλ/r`); the Poisson model is not
formalized. "Costs less" means that some commitment gives a strictly smaller cost; commitments
are real. `o(r)` is little-o along `𝓝[>] 0` with `lam`, `B` fixed. Cube roots are `Real.rpow`
of nonnegative numbers. The model's reset cost is positive; `B = 0` is also allowed, and no sign
is imposed on `C`. -/
theorem theorem_2_bounds_on_payment_rates :
    (∀ lam r B C : ℝ, 0 < lam → 0 < r → 0 ≤ B →
        (∃ m : ℝ, 0 < m ∧ uniCost B r lam m < onChainCost C r lam) →
        Real.log (1 + B * Real.log (1 + r / lam)) < C) ∧
    (∀ lam B : ℝ, 0 < lam → 0 ≤ B →
        (fun r : ℝ => Real.log (1 + B * Real.log (1 + r / lam)) - B * r / lam)
          =o[𝓝[>] 0] (fun r : ℝ => r)) ∧
    (∀ lam r B C : ℝ, 0 < lam → 0 < r → 0 ≤ B →
        (∃ l1 l2 : ℝ, 0 < l1 ∧ 0 < l2 ∧
            bidiCost B r lam lam l1 l2 < 2 * onChainCost C r lam) →
        3 * (B * kappa r lam ^ 4 / 4) ^ (1 / 3 : ℝ) - B / 12 * kappa r lam ^ 2 < C) ∧
    (∀ lam B : ℝ, 0 < lam → 0 ≤ B →
        (fun r : ℝ => (3 * (B * kappa r lam ^ 4 / 4) ^ (1 / 3 : ℝ) - B / 12 * kappa r lam ^ 2)
            - (3 * (B * r ^ 2 / (4 * lam ^ 2)) ^ (1 / 3 : ℝ) - B * r / (12 * lam)))
          =o[𝓝[>] 0] (fun r : ℝ => r)) := by sorry

end LightningNetwork.RateBounds
