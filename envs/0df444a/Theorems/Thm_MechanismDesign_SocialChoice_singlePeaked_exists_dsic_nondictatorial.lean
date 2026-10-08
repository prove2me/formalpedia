-- Prove2me | Theorems.Thm_MechanismDesign_SocialChoice_singlePeaked_exists_dsic_nondictatorial
-- name    : MechanismDesign.SocialChoice.singlePeaked_exists_dsic_nondictatorial
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-03T04:05:48.292139+00:00
-- url     : https://prove2.me/theorems/b403e7e8-5024-471e-9adc-4ae5697a8084
-- title:
--   Proposition 8.6 -- on single-peaked domains there are strategy-proof non-dictatorial mechanisms
-- statement:
--   Let $I$ be a finite set of at least two agents and $A$ a finite set of at least three alternatives, labelled by a fixed bijection with $\{1,\dots,K\}$, and let $\hat{\mathcal R}$ be the set of preferences that are single-peaked with respect to this labelling. Then there is a direct mechanism $f$ on the single-peaked domain $\hat{\mathcal R}^N$ such that
--
--   1. the range of $f$ on $\hat{\mathcal R}^N$ is $A$;
--   2. $f$ is dominant strategy incentive-compatible on $\hat{\mathcal R}^N$:
--   $$f(R_i,R_{-i})\;R_i\;f(R_i',R_{-i})\qquad\text{for all } i,\ R\in\hat{\mathcal R}^N,\ R_i'\in\hat{\mathcal R};$$
--   3. $f$ is not dictatorial on $\hat{\mathcal R}^N$.
--
--   The book's witness is the median voting mechanism, which picks the median of the agents' peaks (with one fixed phantom peak when the number of agents is even). The proposition shows that the Gibbard–Satterthwaite impossibility depends on the unrestricted domain.
--
--   **Formalization Note** The hypothesis that there are at least two agents is added: with a single agent every mechanism with full range that is strategy-proof selects that agent's peak and is therefore dictatorial, so the page's claim needs $N\ge2$. The page's hypothesis "the range of $f$ is $A$" is placed in the conclusion, as a property of the mechanism exhibited. Single-peakedness uses the corrected left-hand clause described in the single-peaked definition.
-- source:
--   Börgers, An Introduction to the Theory of Mechanism Design, Oxford University Press 2015, DOI 10.1093/acprof:oso/9780199734023.001.0001, p.150, Proposition 8.6 (single-peaked preferences defined on p.149)

import Mathlib
import Definitions.Def_MechanismDesign_SocialChoice_Model
import Definitions.Def_MechanismDesign_SocialChoice_SinglePeaked

namespace MechanismDesign.SocialChoice

/-- **Proposition 8.6** (Börgers, p.150): suppose that `A` has at least three elements. If
preferences are single-peaked with respect to a fixed labelling `lab` of the alternatives, then
there is a direct mechanism on the single-peaked domain whose range is `A`, which is dominant
strategy incentive-compatible, and which is not dictatorial.

The hypothesis `2 ≤ Fintype.card ι` is added: with a single agent every onto dominant strategy
incentive-compatible mechanism picks that agent's peak and is dictatorial, so the page's claim
("obviously nondictatorial") needs at least two agents. -/
theorem singlePeaked_exists_dsic_nondictatorial {ι A : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype A] {K : ℕ} (lab : A ≃ Fin K) (hA : 3 ≤ Fintype.card A)
    (hN : 2 ≤ Fintype.card ι) :
    ∃ f : DirectMechanism ι A,
      HasFullRangeOn (SinglePeaked lab) f ∧
      IsDSICOn (SinglePeaked lab) f ∧
      ¬ IsDictatorialOn (SinglePeaked lab) f := by sorry

end MechanismDesign.SocialChoice
