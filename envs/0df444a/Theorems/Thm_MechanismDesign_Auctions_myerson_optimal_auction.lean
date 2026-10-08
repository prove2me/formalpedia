-- Prove2me | Theorems.Thm_MechanismDesign_Auctions_myerson_optimal_auction
-- name    : MechanismDesign.Auctions.myerson_optimal_auction
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-02T23:45:37.188643+00:00
-- url     : https://prove2.me/theorems/20ccaff5-583e-45b9-bae4-c92bfc132080
-- title:
--   Proposition 3.4 (Myerson, 1981) -- the revenue-maximizing single-unit auction
-- statement:
--   Consider the single-unit auction environment with $N \ge 2$ buyers whose independent valuations have densities $f_i > 0$ on $[\underline\theta,\bar\theta]$, and suppose every distribution is **regular**: the virtual valuation
--   $$\psi_i(\theta_i) = \theta_i - \frac{1-F_i(\theta_i)}{f_i(\theta_i)}$$
--   is strictly increasing on $[\underline\theta,\bar\theta]$ for every $i$ (Assumption 3.1). Consider the class of well-defined, incentive-compatible and individually rational direct mechanisms, and the seller's expected revenue $\mathbb E\big[\sum_i t_i(\theta)\big]$.
--
--   **Proposition 3.4 (Myerson, 1981).** A mechanism of this class exists that satisfies (i) for every $\theta \in \Theta$ and (ii) for every $\theta_i$; and a mechanism of this class maximizes the seller's expected revenue over the class if and only if, for every buyer $i$,
--
--   (i) for almost every $\theta \in \Theta$,
--   $$q_i(\theta) = \begin{cases} 1 & \text{if } \psi_i(\theta_i) > 0 \text{ and } \psi_i(\theta_i) > \psi_j(\theta_j) \text{ for all } j \in I \text{ with } j \ne i,\\ 0 & \text{otherwise;}\end{cases}$$
--
--   (ii) for every $\theta_i \in [\underline\theta,\bar\theta]$,
--   $$T_i(\theta_i) = \theta_i Q_i(\theta_i) - \int_{\underline\theta}^{\theta_i} Q_i(x)\,dx.$$
--
--   The optimal auction allocates the good to the buyer with the highest virtual valuation, provided it is positive, and charges interim payments that leave the lowest type zero utility. With asymmetric distributions it may sell to a buyer who does not have the highest value; with symmetric distributions it is implemented by a first- or second-price auction with reserve price $\psi^{-1}(0)$.
--
--   **Formalization Note** The book states (i) "for all $\theta \in \Theta$". It notes itself (p.40) that ties $\psi_i(\theta_i) = \psi_j(\theta_j)$ are a zero-probability event that affects neither incentives nor revenue; changing $q$ on any null set leaves an optimal mechanism optimal, so the literal "only if" direction is false and (i) is stated for almost every $\theta$ with respect to the prior. The existence of an admissible mechanism satisfying (i) at every $\theta$ (the book takes $t_i(\theta) = T_i(\theta_i)$, p.41) is stated separately, so the characterization is not vacuous. Mechanisms are required to be measurable with integrable payments, the book's implicit convention.
-- source:
--   Börgers, An Introduction to the Theory of Mechanism Design, Oxford University Press 2015, DOI 10.1093/acprof:oso/9780199734023.001.0001, p.41, Proposition 3.4

import Mathlib
import Definitions.Def_MechanismDesign_Auctions_Model

open MeasureTheory

namespace MechanismDesign.Auctions

/-- Proposition 3.4 (Myerson, 1981), p.41. Under regularity (Assumption 3.1) there is an
incentive-compatible, individually rational direct mechanism with Myerson's allocation rule
(i) and the payments (ii) `T_i(θ_i) = θ_i Q_i(θ_i) − ∫_{θ̲}^{θ_i} Q_i(x) dx`; and among all
incentive-compatible, individually rational direct mechanisms, a mechanism maximizes the
seller's expected revenue if and only if its allocation rule agrees with (i) for almost every
`θ` and its interim payments satisfy (ii) for every `θ_i`. (The page says "for all `θ ∈ Θ`";
ties `ψ_i(θ_i) = ψ_j(θ_j)` are a null event, so the characterization holds almost everywhere.) -/
theorem myerson_optimal_auction {ι : Type*} [Fintype ι] [DecidableEq ι] (E : Environment ι)
    (hreg : E.Regular) :
    (∃ m : DirectMechanism E, m.Admissible ∧
      (∀ i, ∀ θ ∈ E.typeSpace, m.q i θ = E.myersonAlloc i θ) ∧
      ∀ i, ∀ x ∈ Set.Icc E.lo E.hi,
        m.interimT i x = x * m.interimQ i x - ∫ y in E.lo..x, m.interimQ i y) ∧
    ∀ m : DirectMechanism E, m.Admissible →
      ((∀ m' : DirectMechanism E, m'.Admissible → m'.revenue ≤ m.revenue) ↔
        ((∀ i, ∀ᵐ θ ∂E.prior, m.q i θ = E.myersonAlloc i θ) ∧
          ∀ i, ∀ x ∈ Set.Icc E.lo E.hi,
            m.interimT i x = x * m.interimQ i x - ∫ y in E.lo..x, m.interimQ i y)) := by sorry

end MechanismDesign.Auctions
