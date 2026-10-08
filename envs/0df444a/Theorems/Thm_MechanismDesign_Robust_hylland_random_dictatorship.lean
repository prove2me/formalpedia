-- Prove2me | Theorems.Thm_MechanismDesign_Robust_hylland_random_dictatorship
-- name    : MechanismDesign.Robust.hylland_random_dictatorship
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-03T05:21:16.278026+00:00
-- url     : https://prove2.me/theorems/46a434c4-ef37-4ff3-89d3-a18f67e9dc15
-- title:
--   Proposition 10.12 -- Hylland's theorem: unanimity with belief-independent equilibria means random dictatorship
-- statement:
--   In the voting environment of §10.11 (two agents, three candidates, lotteries as outcomes, private and strict von Neumann–Morgenstern utilities, every strict utility attained by some payoff type), let $(S_1,S_2,g)$ be a finite mechanism and $\sigma^*$ a belief-independent Bayesian equilibrium of it on a type space $\mathcal T$ with a large variety of certainties. Then
--
--   $$(S_1,S_2,g),\ \sigma^* \text{ satisfy positive and negative unanimity} \iff \text{they are a random dictatorship.}$$
--
--   This is a relative of the Gibbard–Satterthwaite theorem for random mechanisms: requiring belief independence leaves only random dictatorships.
--
--   **Formalization Note** The book's "of G" in the statement refers to the mechanism $(S_1,S_2,g)$.
-- source:
--   Börgers, An Introduction to the Theory of Mechanism Design, Oxford University Press 2015, DOI 10.1093/acprof:oso/9780199734023.001.0001, p.196, Proposition 10.12 (Hylland 1980, Theorem 1*; Dutta, Peters and Sen 2007, 2008)

import Mathlib
import Definitions.Def_MechanismDesign_Robust_Voting

open scoped ENNReal

namespace MechanismDesign.Robust

/-- Proposition 10.12 (Börgers p.196; Hylland 1980, as corrected by Dutta, Peters and Sen). In the
voting environment of §10.11 (two agents, candidates `{a, b, c}`, lotteries as outcomes, private
strict von Neumann–Morgenstern utilities, every strict utility attained by a payoff type), a
finite mechanism `(S_1, S_2, g)` and a belief-independent Bayesian equilibrium `σ` on a type space
with a large variety of certainties satisfy positive and negative unanimity if and only if they
are a random dictatorship. -/
theorem hylland_random_dictatorship {Θ T S : Fin 2 → Type*} [∀ i, Fintype (S i)]
    (vu : ∀ i, Θ i → Candidate → ℝ) (henv : IsVotingEnvironment vu)
    (ts : TypeSpace Θ T) (hlv : ts.HasLargeVarietyOfCertainties)
    (M : Mechanism S Candidate) (σ : ∀ i, T i → PMF (S i))
    (hσ : IsBayesEq ts (votingUtility vu) M σ) (hbi : IsBeliefIndependent ts σ) :
    (PositiveUnanimity ts vu M σ ∧ NegativeUnanimity ts vu M σ) ↔
      IsRandomDictatorship ts vu M σ := by sorry

end MechanismDesign.Robust
