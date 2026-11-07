-- Prove2me | Theorems.Thm_FriedgutCoalition_claim_4_6
-- name    : FriedgutCoalition.claim_4_6
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T21:35:56.42128+00:00
-- url     : https://prove2.me/theorems/38d77a89-e0e6-43fb-bc4b-8add6d132f5b
-- title:
--   Claim 4.6 — $\mathbf J^0(f,\mathbf A)\le\mathbf J^0(f)+2pr\cdot n^2$
-- statement:
--   Let $f:[r]^n\to\{0,1\}$ be monotone and $p\in(0,1/2)$ (the standing assumptions of §4), fix a nondecreasing $a\in[r]^\ell$ with the property of Lemma 4.3, and let $\mathbf A$ be the law of $\phi_a(y)$ for $y\sim\mu_p^\ell$. Then
--
--   $$\mathbf J^0(f,\mathbf A)\le\mathbf J^0(f)+2pr\cdot n^2,$$
--
--   where $\mathbf J^0(f)$ is the total influence towards $0$ under the uniform distribution on $[r]^n$.
--
--   Together with Claim 4.2 this gives item 3 of Lemma 3.5.
--
--   Differences from the source:
--   - encoding: "fix a sequence a that satisfies the properties in Lemma 4.3" → hypotheses Monotone a and ∀ i, |selLaw p a i − 1/r| ≤ 2p; reason: the properties of Lemma 4.3 as hypotheses on a; no choice function
--   - encoding: r ∈ ℕ with the value 1 ∈ [r] used (Definition 4.1) → [NeZero r], i.e. r ≥ 1; reason: [r] must be nonempty for ϕ_a(0^ℓ) = 1 and for 1/r; the source's r is the alphabet size of f : [r]ⁿ → {0,1}
--   - encoding: {0,1}, [n], [r] = {1,…,r} → Bool (false < true), Fin n, Fin r (the value 1 of [r] is 0 : Fin r, the value r is its top); reason: Lean conventions; the same instances
-- source:
--   Chattopadhyay, Gurumukhani, A Resolution of Friedgut's Conjecture on Influential Coalitions, arXiv:2609.16401 (held file sha256 51f298ff…), Claim 4.6, p.14 ("Fix a sequence a that satisfies the properties in Lemma 4.3", p.13; standing assumptions of §4, p.10)

import Mathlib
import Definitions.Def_FriedgutCoalition_coalProb
import Definitions.Def_FriedgutCoalition_maxSel

namespace FriedgutCoalition

/-- **Claim 4.6** (Chattopadhyay–Gurumukhani, arXiv:2609.16401 (held file sha256 51f298ff…), p.14). Let `f : [r]ⁿ → {0,1}` be monotone,
`p ∈ (0, 1/2)` (§4's standing assumptions, p.10), and fix a nondecreasing `a ∈ [r]^ℓ` satisfying the
properties of Lemma 4.3 (p.13), with `A` the law of `ϕ_a(y)`, `y ∼ µ^ℓ_p`. Then
`J⁰(f, A) ≤ J⁰(f) + 2pr · n²`.

**Formalization Note.** `[r]` is `Fin r` (`[NeZero r]`), `A` is `selLaw p a`, `J⁰(f, σ)` is
`totalToward σ f false`, and `J⁰(f)` uses the uniform weights `unif r`. -/
theorem claim_4_6 {n ℓ r : ℕ} [NeZero r] (p : ℝ) (hp0 : 0 < p) (hp : p < 1 / 2)
    (f : (Fin n → Fin r) → Bool) (hf : Monotone f)
    (a : Fin ℓ → Fin r) (ha : Monotone a)
    (hA : ∀ i : Fin r, |selLaw p a i - 1 / (r : ℝ)| ≤ 2 * p) :
    totalToward (selLaw p a) f false ≤
      totalToward (unif r) f false + 2 * p * r * (n : ℝ) ^ 2 := by sorry

end FriedgutCoalition
