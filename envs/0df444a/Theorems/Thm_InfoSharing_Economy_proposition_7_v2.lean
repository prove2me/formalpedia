-- Prove2me | Theorems.Thm_InfoSharing_Economy_proposition_7_v2
-- name    : InfoSharing.Economy.proposition_7_v2
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-10-06T06:20:50.300311+00:00
-- url     : https://prove2.me/theorems/04d2d0cd-bef6-461e-8a55-97062622b5bb
-- title:
--   Proposition 7 — equilibrium information sharing under concurrent and sequential contracting (production economy), with the paper's concurrent-outcome selection
-- statement:
--   For every $\phi>0$ there are thresholds $c_e^C,c_e^S\in(1/(1+\phi),2/(1+\phi))$, depending only on $\phi$, such that the following holds. Let $0<c_e<2/(1+\phi)$, put $c=-c_e$, and let $a,b$ be reals. Let $(\theta,Y)$ satisfy the signal model with variance $\sigma^2$ and weight $\beta=\beta(t,\sigma)$, let $E$ be any family of pricing equilibria with payoff table $P$, and let $n_e^Z$ be the number of informed manufacturers under concurrent ($Z=C$) or sequential ($Z=S$, for either first mover) information contracting. Then
--   $$n_e^Z=\begin{cases}0 & c_e<1/(1+\phi),\\ 2 & 1/(1+\phi)\le c_e<c_e^Z,\\ 1 & c_e^Z\le c_e<2/(1+\phi),\end{cases}$$
--   in the two-clause form: on each region the stated value of $n$ is attained by some outcome, and on the interior of the region it is the only value attained (at a boundary point the retailer is indifferent between outcomes). Precisely, with $O$ the set of values of $n$ over all concurrent outcomes (resp. all SPEs with first mover $k$): $O=\{0\}$ for $c_e<1/(1+\phi)$; $2\in O$ on $[1/(1+\phi),c_e^Z)$ and $O=\{2\}$ on its interior; $1\in O$ on $[c_e^Z,2/(1+\phi))$ and $O=\{1\}$ on its interior.
--
--   Under production economy the retailer shares information exactly when the economy is large relative to competition, whichever contracting sequence is used.
--
--   **Formalization Note.** The production economy model takes $c=-c_e$ with $0<c_e<2/(1+\phi)$ (the Assumption of p. 251). The ex ante profits are those of an equilibrium of the pricing game on the signal model, not the closed forms (the closed forms are the content of the §4.2 milestones). The production cost is the uncapped quadratic $bq-c_eq^2$ (the paper's cap at $\bar q=b/(2c_e)$ is assumed never to bind, footnote 11, p. 251). At $c_e=1/(1+\phi)$ every profit is independent of $n$, so all three values are attained there. **What changed.** The retired version used a captain-built outcome concept (a pure equilibrium whose retailer payoff equals the supremum over Pareto-optimal equilibria of Table 1), which is not attained at the value of $c_e$ where the willingness-to-pay levels $\pi_M^I(1)-\pi_M(0)$ and $\pi_M^I(2)-\pi_M^U(1)$ coincide, so no closed threshold could satisfy both the two-buyer and the one-buyer clauses (accepted disproof). Concurrent outcomes are now those of `Def_InfoSharing_Economy_IsConcurrentOutcome_v2`: the paper's own selection, a nonnegative payment and a pure equilibrium of Table 1 at it that maximize the retailer's payoff over all payments and pure equilibria, an indifferent manufacturer accepting — exactly the computation of the proof of Proposition 7 (p. 261), which charges $T=\pi_M^I(1)-\pi_M(0)$ for one buyer although $(U,U)$ is also an equilibrium there. Sequential outcomes (`SeqOptN`) are unchanged. **Correction of the paper.** The single value $c_e^*=\frac{2+3\phi}{(1+2\phi)(1+\phi)}$ (which lies in $(1/(1+\phi),2/(1+\phi))$) is excluded: there the slope of the best response (2) equals $-1$, the pricing stage has a continuum of equilibria with different ex ante profits, and Lemma 1's uniqueness claim, on which the payoff table rests, fails.
-- source:
--   Shang, Ha & Tong, Information Sharing in a Supply Chain with a Common Retailer, Management Sci. 62(1) 2016, p. 256, Proposition 7 (thresholds and the concurrent-contracting computation in the proof of Proposition 7, p. 261)

import Mathlib
import Definitions.Def_InfoSharing_Shared_IsSignalModel
import Definitions.Def_InfoSharing_Shared_PayoffTable
import Definitions.Def_InfoSharing_Economy_IsConcurrentOutcome_v2
import Definitions.Def_InfoSharing_Shared_IsSequentialSPE
open MeasureTheory
open InfoSharing.Shared

namespace InfoSharing.Economy

/-- **Proposition 7** (Shang, Ha & Tong 2016, p. 256), production economy (`c = −c_e`) under
the Assumption `c_e < 2/(1+φ)`: the equilibrium number `n_e^Z` of informed manufacturers under
concurrent (`Z = C`) and sequential (`Z = S`, either first mover `k`) information contracting,
with thresholds `c_e^C`, `c_e^S` that depend only on `φ`. `ConcOptN P` and `SeqOptN P k` are the
sets of values of `n` over all outcomes; on each region `n` is attained, and it is the only
value in the region's interior (at the region boundaries the retailer is indifferent).

Corrected version: the statement is unchanged, but concurrent outcomes are those of the
corrected module `Def_InfoSharing_Economy_IsConcurrentOutcome_v2`, the paper's own selection
(the retailer-optimal payment and pure equilibrium of Table 1, an indifferent manufacturer
accepting), instead of the retired supremum over Pareto-optimal equilibria, which was not
attained where the two willingness-to-pay levels coincide.

**Correction.** The value `c_e = (2+3φ)/((1+2φ)(1+φ))` is excluded: there the best-response
slope in (2) is `−1`, the pricing stage has a continuum of equilibria with different ex ante
profits, and Lemma 1's uniqueness (on which the paper's payoff table rests) fails. -/
theorem proposition_7_v2 :
    ∀ φ : ℝ, 0 < φ → ∃ cC cS : ℝ,
    1 / (1 + φ) < cC ∧ cC < 2 / (1 + φ) ∧ 1 / (1 + φ) < cS ∧ cS < 2 / (1 + φ) ∧
    ∀ (ce c a b σ β : ℝ) {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (θ Y : Ω → ℝ)
      (E : (Fin 2 → Status) → PricingProfile),
      c = -ce → 0 < ce → ce < 2 / (1 + φ) → ce ≠ (2 + 3 * φ) / ((1 + 2 * φ) * (1 + φ)) →
      IsSignalModel μ θ Y σ β →
      IsPricingEqFamily μ θ Y a b c φ β E →
      let P := payoffTable μ θ Y a b c φ E
      ((ce < 1 / (1 + φ) → ConcOptN P = {0}) ∧
         (1 / (1 + φ) ≤ ce → ce < cC → 2 ∈ ConcOptN P) ∧
         (1 / (1 + φ) < ce → ce < cC → ConcOptN P = {2}) ∧
         (cC ≤ ce → 1 ∈ ConcOptN P) ∧
         (cC < ce → ConcOptN P = {1})) ∧
      ∀ k : Fin 2,
        ((ce < 1 / (1 + φ) → SeqOptN P k = {0}) ∧
           (1 / (1 + φ) ≤ ce → ce < cS → 2 ∈ SeqOptN P k) ∧
           (1 / (1 + φ) < ce → ce < cS → SeqOptN P k = {2}) ∧
           (cS ≤ ce → 1 ∈ SeqOptN P k) ∧
           (cS < ce → SeqOptN P k = {1})) := by sorry

end InfoSharing.Economy
