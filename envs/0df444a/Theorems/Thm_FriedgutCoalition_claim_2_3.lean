-- Prove2me | Theorems.Thm_FriedgutCoalition_claim_2_3
-- name    : FriedgutCoalition.claim_2_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T21:35:15.700042+00:00
-- url     : https://prove2.me/theorems/3bdd8fc1-2bdb-4cf7-bb14-ba8be9e336b0
-- title:
--   Claim 2.3 — discretizing a monotone function on $[0,1]^n$ to $[r]^n$ costs at most $n/r$
-- statement:
--   Let $n,r\in\mathbb N$ with $r\ge2$. For every monotone $f:[0,1]^n\to\{0,1\}$ there is a monotone $g:[r]^n\to\{0,1\}$ such that
--
--   $$\big|\mathbb E[f]-\mathbb E[g]\big|\le\frac nr\qquad\text{and}\qquad\big|\mathbf P^b_S(g)-\mathbf P^b_S(f)\big|\le\frac nr$$
--
--   for every $S\subseteq[n]$ and $b\in\{0,1\}$. Expectations and coalition probabilities on $[0,1]^n$ are under the uniform measure, on $[r]^n$ under the uniform distribution.
--
--   With $r$ of order $n/\varepsilon$ this transfers coalition bounds from the finite alphabet $[r]$ to the solid cube.
--
--   Differences from the source:
--   - encoding: P^b_S(f) on [0,1]ⁿ, the probability of the success event → cubeCoalProb: 1 minus the outer measure of the failure set (the inner measure of the success event); reason: equal to the source's value whenever the success event is Lebesgue measurable, which p.5 proves for monotone and Borel f; never larger, so lower bounds are not weakened
--   - encoding: E[f] on [0,1]ⁿ → cubeMean: the measure of {x | f x = 1}; reason: equal to E[f] whenever {f = 1} is Lebesgue measurable (monotone or Borel f); avoids the Bochner integral's junk value
--   - encoding: {0,1}, [n], [r] = {1,…,r} → Bool (false < true), Fin n, Fin r (the value 1 of [r] is 0 : Fin r, the value r is its top); reason: Lean conventions; the same instances
-- source:
--   Chattopadhyay, Gurumukhani, A Resolution of Friedgut's Conjecture on Influential Coalitions, arXiv:2609.16401 (held file sha256 51f298ff…), Claim 2.3, p.7

import Mathlib
import Definitions.Def_FriedgutCoalition_coalProb
import Definitions.Def_FriedgutCoalition_cubeCoalProb

namespace FriedgutCoalition

/-- **Claim 2.3** (Chattopadhyay–Gurumukhani, arXiv:2609.16401 (held file sha256 51f298ff…), p.7). For all `n, r ∈ ℕ` with `r ≥ 2` and
every monotone `f : [0,1]ⁿ → {0,1}` there is a monotone `g : [r]ⁿ → {0,1}` with
`|E[f] − E[g]| ≤ n/r` and `|P^b_S(g) − P^b_S(f)| ≤ n/r` for every `S ⊆ [n]` and `b ∈ {0,1}`.

**Formalization Note.** `[r]ⁿ` is `Fin n → Fin r` with the uniform distribution; on the cube `E[·]`
is `cubeMean` and `P^b_S` is `cubeCoalProb`. -/
theorem claim_2_3 (n r : ℕ) (hr : 2 ≤ r) (f : (Fin n → unitInterval) → Bool) (hf : Monotone f) :
    ∃ g : (Fin n → Fin r) → Bool, Monotone g ∧
      |cubeMean f - outProb (unif r) g true| ≤ (n : ℝ) / r ∧
      ∀ (S : Finset (Fin n)) (b : Bool),
        |coalProb (unif r) g S b - cubeCoalProb f S b| ≤ (n : ℝ) / r := by sorry

end FriedgutCoalition
