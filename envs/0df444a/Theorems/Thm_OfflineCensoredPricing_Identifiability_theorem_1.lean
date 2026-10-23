-- Prove2me | Theorems.Thm_OfflineCensoredPricing_Identifiability_theorem_1
-- name    : OfflineCensoredPricing.Identifiability.theorem_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T12:33:46.85821+00:00
-- url     : https://prove2.me/theorems/7daebff5-fc3e-4e91-8e84-4bfd5d2a4497
-- title:
--   Theorem 1, p. 13 — identifiable iff p*_max = p*_min; D2ACD is near-optimal when they coincide, every price loses ≥ γb/(√γ+1)²(p*_max − p*_min)² otherwise
-- statement:
--   **Theorem 1 (Necessary and sufficient condition for identifiability).** For any inventory level $y$, price range $[\underline p,\bar p]$ and base demand distribution $F_\xi$, the data-driven pricing problem with censored offline data of observable boundary $\lambda$ is identifiable if and only if
--   $$p^*_{\max} = p^*_{\min}. \qquad (3)$$
--
--   Precisely, for every instance satisfying the standing assumptions of the model:
--   1. D2ACD always outputs a price in $[\underline p,\bar p]$, and if $p^*_{\max} = p^*_{\min}$ it is near-optimal: for every $\varepsilon > 0$, $\lim_{N\to\infty}\mathbb P[\max_{F\in\mathcal F}\{R_F(p^*_F) - R_F(p^{\mathrm{D2ACD}})\} < \varepsilon] = 1$;
--   2. if $p^*_{\max} \ne p^*_{\min}$, the constant $c = \frac{\gamma b}{(\sqrt\gamma+1)^2}(p^*_{\max} - p^*_{\min})^2$ is positive and every price $p \in [\underline p,\bar p]$ has worst-case revenue loss $\max_{F\in\mathcal F}\{R_F(p^*_F) - R_F(p)\} \ge c$, so no data-driven algorithm can be near-optimal;
--   3. the problem is identifiable (Definition 1) if and only if $p^*_{\max} = p^*_{\min}$.
--
--   This is the first main result of the paper. Censoring hides the distribution of $\xi$ on $[\lambda,\infty)$; the theorem says exactly when this lost information is irrelevant for pricing.
--
--   **Formalization Note** Definition 1 fixes the whole instance, including $b$ and the historical pairs, before asking for an algorithm, so a constant algorithm equal to $p^*_{\max}$ witnesses item 3 whenever $p^*_{\max} = p^*_{\min}$ (its worst-case loss is $0$ by Proposition 7). Item 1 is what the paper's proof (Appendix C.2) establishes and what the paper means: the witness is D2ACD, a fixed function of the censored sales and the public inputs only. Item 2 is the quantitative content of the "only if" direction (Proposition 6). The limit in (2) is over all sample-size vectors with $\min_i N_i \to \infty$, and failure probabilities are outer probabilities; item 1 is stated without the data assumption $\hat\gamma_i > 0$, whose failure probability tends to $0$. The type `Fin K` is assumed nonempty (implied by $K \ge 2$) so that D2ACD's selected index is well typed.
-- source:
--   Bu, Simchi-Levi & Wang, SSRN 3619625 (PDF of 2021-08-23), p. 13, Theorem 1, (3) (with its proof, online Appendix C.2, p. 37; Definition 1, (2), p. 12)

import Mathlib
import Definitions.Def_OfflineCensoredPricing_Identifiability_Model
import Definitions.Def_OfflineCensoredPricing_Identifiability_D2ACD

namespace OfflineCensoredPricing.Identifiability

open MeasureTheory Set

/-- **Theorem 1** (Necessary and sufficient condition for identifiability, p. 13; proof in Appendix
C.2, p. 37). For any inventory level `y`, price range `[p̲, p̄]` and base demand distribution `F_ξ`, the
data-driven problem is identifiable if and only if `p*_max = p*_min` (3). Stated in three parts:
1. D2ACD outputs feasible prices, and if `p*_max = p*_min` it is near-optimal in the sense of (2);
2. if `p*_max ≠ p*_min`, every feasible price has worst-case revenue loss at least the positive constant
   `γb/(√γ + 1)² (p*_max − p*_min)²`;
3. identifiable (Definition 1) iff `p*_max = p*_min`. -/
theorem theorem_1 {K : ℕ} [NeZero K] (I : Instance K) (hI : I.Standing) :
    (Valid I.toPublic (d2acd I.toPublic) ∧
      (pStarMax I = pStarMin I → NearOptimal I (d2acd I.toPublic))) ∧
    (pStarMax I ≠ pStarMin I →
      0 < gam I * I.b / (Real.sqrt (gam I) + 1) ^ 2 * (pStarMax I - pStarMin I) ^ 2 ∧
      ∀ q ∈ Icc I.plo I.phi,
        gam I * I.b / (Real.sqrt (gam I) + 1) ^ 2 * (pStarMax I - pStarMin I) ^ 2 ≤
          worstLoss I q) ∧
    (Identifiable I ↔ pStarMax I = pStarMin I) := by sorry

end OfflineCensoredPricing.Identifiability
