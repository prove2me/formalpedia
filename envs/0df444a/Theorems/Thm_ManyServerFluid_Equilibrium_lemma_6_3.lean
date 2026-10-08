-- Prove2me | Theorems.Thm_ManyServerFluid_Equilibrium_lemma_6_3
-- name    : ManyServerFluid.Equilibrium.lemma_6_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T07:51:19.384472+00:00
-- url     : https://prove2.me/theorems/8d2ab0cc-f1a7-4413-aba3-9231df91e269
-- title:
--   Lemma 6.3 — with a finite second moment, ∫_[0,t] (∫_{T+t−s}^∞ (1 − G(r)) dr) U(ds) ≤ ε for all T ≥ T_ε, (6.11)
-- statement:
--   Suppose the service distribution has a finite second moment, $\int_{[0,\infty)}x^2g(x)\,dx<\infty$, and let $U$ be the renewal measure of $G$. Then for every $\varepsilon>0$ there is $T_\varepsilon\in(0,\infty)$ such that
--   $$\int_{[0,t]}\Big(\int_{T+t-s}^{\infty}(1-G(r))\,dr\Big)U(ds)\le\varepsilon\qquad\text{for all }T\ge T_\varepsilon\text{ and all }t\ge0.\qquad(6.11)$$
--
--   The estimate is uniform in $t$. In the proof of Theorem 3.9(2) it bounds, for all times at once, the difference between the entry process of the fluid solution restarted at a time $T$ when the system is full and the function $Z$ of the reference system of Lemma 6.2.
--
--   **Formalization Note** In (6.11) the variable $t$ is free and the paper's quantifier is implicit; the proof bounds the left-hand side uniformly in $t$, and the proof of Theorem 3.9 uses it "for every $t\in[0,\infty)$" (6.14). The statement therefore places "for all $t\ge0$" after $\exists T_\varepsilon$. Both integrals are lower Lebesgue integrals in $[0,\infty]$, so the bound also asserts finiteness. The second moment is the integrability of $x\mapsto x^2g(x)$.
-- source:
--   Kaspi and Ramanan, Law of Large Numbers Limits for Many-Server Queues, Ann. Appl. Probab. 21(1) (2011), p. 109, Lemma 6.3, (6.11)

import Mathlib
import Definitions.Def_ManyServerFluid_Equilibrium_Model
import Definitions.Def_ManyServerFluid_Equilibrium_Renewal
open MeasureTheory Filter Topology Set BoundedContinuousFunction

namespace ManyServerFluid.Equilibrium

/-- Lemma 6.3 (p. 109): under a finite second moment,
∫_[0,t] (∫_{T+t−s}^∞ (1 − G(r)) dr) U(ds) ≤ ε for all T ≥ T_ε, uniformly in t ≥ 0. -/
theorem lemma_6_3 (S : ServiceLaw) (h2 : Integrable (fun x => x ^ 2 * S.g x)) :
    ∀ ε : ℝ, 0 < ε → ∃ Tε : ℝ, 0 < Tε ∧ ∀ T, Tε ≤ T → ∀ t, 0 ≤ t →
      ∫⁻ s in Icc 0 t, (∫⁻ r in Ioi (T + t - s), ENNReal.ofReal (1 - S.G r)) ∂S.renewalMeasure
        ≤ ENNReal.ofReal ε := by sorry

end ManyServerFluid.Equilibrium
