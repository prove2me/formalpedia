-- Prove2me | Theorems.Thm_FriedgutCoalition_claim_2_2
-- name    : FriedgutCoalition.claim_2_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T21:35:25.346946+00:00
-- url     : https://prove2.me/theorems/c41743bb-8b07-4382-9650-198b54b6ff82
-- title:
--   Claim 2.2 — monotonization keeps the expectation and does not increase coalition power
-- statement:
--   **(a)** For every Borel measurable $f:[0,1]^n\to\{0,1\}$ there is a monotone $g:[0,1]^n\to\{0,1\}$ with $\mathbb E[g]=\mathbb E[f]$ and
--
--   $$\mathbf P^b_S(g)\le\mathbf P^b_S(f)\qquad\text{for all }S\subseteq[n],\ b\in\{0,1\}.$$
--
--   **(b)** Furthermore, for every $f:[r]^n\to\{0,1\}$ there is a monotone $g:[r]^n\to\{0,1\}$ with the same properties, expectations and coalition probabilities taken under the uniform distribution on $[r]^n$.
--
--   Here $\mathbf P^b_S$ is the probability that the coalition $S$, choosing its values after the other coordinates are drawn, forces the output $b$. The claim reduces every lower bound on coalition power to monotone functions.
--
--   Differences from the source:
--   - encoding: Borel measurable → Measurable f for the product σ-algebra on Fin n → unitInterval (the Borel σ-algebra) and the discrete σ-algebra on Bool; reason: Lean convention; the same functions
--   - encoding: P^b_S(f) on [0,1]ⁿ, the probability of the success event → cubeCoalProb: 1 minus the outer measure of the failure set (the inner measure of the success event); reason: equal to the source's value whenever the success event is Lebesgue measurable, which p.5 proves for monotone and Borel f; never larger, so lower bounds are not weakened
--   - encoding: E[f] on [0,1]ⁿ → cubeMean: the measure of {x | f x = 1}; reason: equal to E[f] whenever {f = 1} is Lebesgue measurable (monotone or Borel f); avoids the Bochner integral's junk value
--   - encoding: {0,1}, [n], [r] = {1,…,r} → Bool (false < true), Fin n, Fin r (the value 1 of [r] is 0 : Fin r, the value r is its top); reason: Lean conventions; the same instances
--   - encoding: r ∈ ℕ (an alphabet [r] = {1,…,r}) → any r : ℕ, including r = 0; reason: at r = 0 and n ≥ 1 the domain [0]ⁿ is empty and part (b) holds trivially; no instance with r ≥ 1 changes
-- source:
--   Chattopadhyay, Gurumukhani, A Resolution of Friedgut's Conjecture on Influential Coalitions, arXiv:2609.16401 (held file sha256 51f298ff…), Claim 2.2, p.6

import Mathlib
import Definitions.Def_FriedgutCoalition_coalProb
import Definitions.Def_FriedgutCoalition_cubeCoalProb

namespace FriedgutCoalition

/-- **Claim 2.2** (Chattopadhyay–Gurumukhani, arXiv:2609.16401 (held file sha256 51f298ff…), p.6). (a) For every Borel measurable
`f : [0,1]ⁿ → {0,1}` there is a monotone `g : [0,1]ⁿ → {0,1}` with `E[g] = E[f]` and
`P^b_S(g) ≤ P^b_S(f)` for all `S ⊆ [n]` and `b`. (b) Furthermore, the same holds for
`f : [r]ⁿ → {0,1}`, with a monotone `g : [r]ⁿ → {0,1}`, under the uniform distribution.

**Formalization Note.** On the cube, `E[·]` is `cubeMean` and `P^b_S` is `cubeCoalProb`; on `[r]ⁿ`
(`Fin n → Fin r`), `E[g] = outProb (unif r) g true` and `P^b_S = coalProb (unif r)`. Part (b) has no
hypothesis on `r`: at `r = 0`, `n ≥ 1` the domain is empty and the claim holds trivially. The claim
does not assert that `g` is Borel, so neither does the statement. -/
theorem claim_2_2 :
    (∀ (n : ℕ) (f : (Fin n → unitInterval) → Bool), Measurable f →
      ∃ g : (Fin n → unitInterval) → Bool, Monotone g ∧ cubeMean g = cubeMean f ∧
        ∀ (S : Finset (Fin n)) (b : Bool), cubeCoalProb g S b ≤ cubeCoalProb f S b) ∧
    (∀ (n r : ℕ) (f : (Fin n → Fin r) → Bool),
      ∃ g : (Fin n → Fin r) → Bool, Monotone g ∧
        outProb (unif r) g true = outProb (unif r) f true ∧
        ∀ (S : Finset (Fin n)) (b : Bool), coalProb (unif r) g S b ≤ coalProb (unif r) f S b) := by sorry

end FriedgutCoalition
