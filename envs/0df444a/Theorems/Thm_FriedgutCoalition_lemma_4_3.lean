-- Prove2me | Theorems.Thm_FriedgutCoalition_lemma_4_3
-- name    : FriedgutCoalition.lemma_4_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T21:36:00.42231+00:00
-- url     : https://prove2.me/theorems/ce13efd5-2da8-41f6-90a6-4ad9047edc8d
-- title:
--   Lemma 4.3 — a max-selector encoding whose law is within $2p$ of uniform
-- statement:
--   Let $r\ge1$ and $p\in(0,1/2)$. There are $\ell\in\mathbb N$ and a nondecreasing sequence $a=(a_1,\dots,a_\ell)\in[r]^\ell$ such that
--
--   $$\Big|\Pr_{y\sim\mu_p^\ell}[\phi_a(y)=i]-\frac1r\Big|\le2p\qquad\text{for all }i\in[r].$$
--
--   So the law $\mathbf A$ of the encoded coordinate approximates the uniform distribution on $[r]$, which is what keeps expectations and coalition probabilities nearly unchanged by the encoding.
--
--   Differences from the source:
--   - encoding: r ∈ ℕ with the value 1 ∈ [r] used (Definition 4.1) → [NeZero r], i.e. r ≥ 1; reason: [r] must be nonempty for ϕ_a(0^ℓ) = 1 and for 1/r; the source's r is the alphabet size of f : [r]ⁿ → {0,1}
-- source:
--   Chattopadhyay, Gurumukhani, A Resolution of Friedgut's Conjecture on Influential Coalitions, arXiv:2609.16401 (held file sha256 51f298ff…), Lemma 4.3, p.12 (standing assumption p ∈ (0,1/2) of §4, p.10)

import Mathlib
import Definitions.Def_FriedgutCoalition_maxSel

namespace FriedgutCoalition

/-- **Lemma 4.3** (Chattopadhyay–Gurumukhani, arXiv:2609.16401 (held file sha256 51f298ff…), p.12). Let `r ≥ 1` and `p ∈ (0, 1/2)` (§4's
standing assumption, p.10). There are `ℓ ∈ ℕ` and a nondecreasing `a = (a₁, …, a_ℓ) ∈ [r]^ℓ` such
that `|Pr_{y∼µ_p}[ϕ_a(y) = i] − 1/r| ≤ 2p` for all `i ∈ [r]`.

**Formalization Note.** `[r]` is `Fin r` (`[NeZero r]`), `ϕ_a` is `maxSel a`, and
`Pr_{y∼µ^ℓ_p}[ϕ_a(y) = i]` is `selLaw p a i`. -/
theorem lemma_4_3 {r : ℕ} [NeZero r] (p : ℝ) (hp0 : 0 < p) (hp : p < 1 / 2) :
    ∃ (ℓ : ℕ) (a : Fin ℓ → Fin r), Monotone a ∧
      ∀ i : Fin r, |selLaw p a i - 1 / (r : ℝ)| ≤ 2 * p := by sorry

end FriedgutCoalition
