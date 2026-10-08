-- Prove2me | Theorems.Thm_MechanismDesign_Auctions_welfare_maximization
-- name    : MechanismDesign.Auctions.welfare_maximization
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-02T23:45:23.532176+00:00
-- url     : https://prove2.me/theorems/773bc623-2ce7-4b35-9a45-392e87ab7044
-- title:
--   Proposition 3.5 -- welfare-maximizing auctions allocate to the highest value
-- statement:
--   Consider the class of well-defined, incentive-compatible, individually rational direct mechanisms in the single-unit auction environment, and expected welfare $\mathbb E\big[\sum_i q_i(\theta)\theta_i\big]$ (Eq. (3.8)).
--
--   **Proposition 3.5.** A mechanism of this class exists that satisfies (i) and (ii) below for all $i$ and all $\theta \in \Theta$; and a mechanism of this class maximizes expected welfare over the class if and only if, for every buyer $i$,
--
--   (i) for almost every $\theta \in \Theta$,
--   $$q_i(\theta) = \begin{cases} 1 & \text{if } \theta_i > \theta_j \text{ for all } j \in I \text{ with } j \ne i,\\ 0 & \text{otherwise;}\end{cases}$$
--
--   (ii) for every $\theta_i \in [\underline\theta,\bar\theta]$,
--   $$T_i(\theta_i) \le \theta_i Q_i(\theta_i) - \int_{\underline\theta}^{\theta_i} Q_i(x)\,dx.$$
--
--   The result needs no regularity assumption. Compared with Proposition 3.4, the welfare-maximizing mechanism always sells and sells to the highest actual (not virtual) value.
--
--   **Formalization Note** The book states (i) "for all $\theta \in \Theta$". Changing $q$ on a null set of type vectors (for instance on ties $\theta_i = \theta_j$) changes neither incentives nor expected welfare, so the literal "only if" direction is false; the characterization is stated for almost every $\theta$ with respect to the prior, and the existence of a mechanism satisfying (i) at every $\theta$ is stated separately.
-- source:
--   Börgers, An Introduction to the Theory of Mechanism Design, Oxford University Press 2015, DOI 10.1093/acprof:oso/9780199734023.001.0001, p.42, Proposition 3.5

import Mathlib
import Definitions.Def_MechanismDesign_Auctions_Model

open MeasureTheory

namespace MechanismDesign.Auctions

/-- Proposition 3.5, p.42: an incentive-compatible, individually rational direct mechanism that
allocates efficiently (`q_i(θ) = 1` if `θ_i > θ_j` for all `j ≠ i`, else `0`) and satisfies
`T_i(θ_i) ≤ θ_i Q_i(θ_i) − ∫_{θ̲}^{θ_i} Q_i(x) dx` exists; and among all incentive-compatible,
individually rational direct mechanisms, a mechanism maximizes expected welfare
`E[∑_i q_i(θ) θ_i]` if and only if it allocates efficiently for almost every `θ` and satisfies
the payment inequality for every `θ_i`. (The page says "for all `θ ∈ Θ`"; ties `θ_i = θ_j` are a
null event, so the characterization holds almost everywhere.) -/
theorem welfare_maximization {ι : Type*} [Fintype ι] [DecidableEq ι] (E : Environment ι) :
    (∃ m : DirectMechanism E, m.Admissible ∧
      (∀ i, ∀ θ ∈ E.typeSpace, m.q i θ = efficientAlloc i θ) ∧
      ∀ i, ∀ x ∈ Set.Icc E.lo E.hi,
        m.interimT i x ≤ x * m.interimQ i x - ∫ y in E.lo..x, m.interimQ i y) ∧
    ∀ m : DirectMechanism E, m.Admissible →
      ((∀ m' : DirectMechanism E, m'.Admissible → m'.welfare ≤ m.welfare) ↔
        ((∀ i, ∀ᵐ θ ∂E.prior, m.q i θ = efficientAlloc i θ) ∧
          ∀ i, ∀ x ∈ Set.Icc E.lo E.hi,
            m.interimT i x ≤ x * m.interimQ i x - ∫ y in E.lo..x, m.interimQ i y)) := by sorry

end MechanismDesign.Auctions
