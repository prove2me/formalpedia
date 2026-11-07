-- Prove2me | Theorems.Thm_FriedgutCoalition_lemma_4_5
-- name    : FriedgutCoalition.lemma_4_5
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T21:36:23.068196+00:00
-- url     : https://prove2.me/theorems/ab507ac5-5e43-4f76-8cce-89f0b754f877
-- title:
--   Lemma 4.5 — $\|\mathbf A-U^r\|_\infty\le2p$ and $|\mathbf A^i-U^r_i|\le pri$
-- statement:
--   Let $r\ge1$ and $p\in(0,1/2)$, and fix a nondecreasing $a\in[r]^\ell$ with the property of Lemma 4.3, $\big|\Pr_{y\sim\mu_p^\ell}[\phi_a(y)=i]-1/r\big|\le2p$ for all $i\in[r]$. Let $\mathbf A$ be the law of $\phi_a(y)$ and $U^r$ the uniform distribution on $[r]$. Then
--
--   1. $\|\mathbf A-U^r\|_\infty\le2p$;
--   2. for all $i\ge1$,
--
--   $$\big|\mathbf A^i-U^r_i\big|\le pri,$$
--
--   where $|\cdot|$ is the statistical distance $\tfrac12\sum|\Pr[\mathbf X=x]-\Pr[\mathbf Y=x]|$ and $\mathbf A^i$, $U^r_i$ are the $i$-fold products.
--
--   With $i=n$ this bounds the cost of replacing the uniform distribution on $[r]^n$ by the encoded law $\mathbf A^n$.
--
--   Differences from the source:
--   - encoding: ‖A − Uʳ‖∞ = max_w |Pr[A = w] − Pr[Uʳ = w]| ≤ 2p → ∀ w, |selLaw p a w − unif r w| ≤ 2p; reason: the same condition on the nonempty finite set [r]
--   - encoding: "fix a sequence a that satisfies the properties in Lemma 4.3" → hypotheses Monotone a and ∀ i, |selLaw p a i − 1/r| ≤ 2p; reason: the properties of Lemma 4.3 as hypotheses on a; no choice function
--   - encoding: the §4 standing assumption "fix a monotone function f : [r]ⁿ → {0,1}" → no f in the statement; reason: neither part of the lemma mentions f; r is kept as the alphabet size
--   - encoding: r ∈ ℕ with the value 1 ∈ [r] used (Definition 4.1) → [NeZero r], i.e. r ≥ 1; reason: [r] must be nonempty for ϕ_a(0^ℓ) = 1 and for 1/r; the source's r is the alphabet size of f : [r]ⁿ → {0,1}
-- source:
--   Chattopadhyay, Gurumukhani, A Resolution of Friedgut's Conjecture on Influential Coalitions, arXiv:2609.16401 (held file sha256 51f298ff…), Lemma 4.5, pp.13–14 ("Fix a sequence a that satisfies the properties in Lemma 4.3", p.13; §2.3, p.7)

import Mathlib
import Definitions.Def_FriedgutCoalition_maxSel
import Definitions.Def_FriedgutCoalition_prodLaw
import Definitions.Def_IsingLTL_BeliefProp_TVDist

namespace FriedgutCoalition

/-- **Lemma 4.5** (Chattopadhyay–Gurumukhani, arXiv:2609.16401 (held file sha256 51f298ff…), pp.13–14). Let `r ≥ 1`, `p ∈ (0, 1/2)`, and fix
a nondecreasing `a ∈ [r]^ℓ` satisfying the properties of Lemma 4.3 (p.13). With `A` the law of
`ϕ_a(y)`, `y ∼ µ^ℓ_p`:
1. `‖A − U_r‖_∞ ≤ 2p`;
2. for all `i ≥ 1`, `|A^i − U_r^i| ≤ pri` (statistical distance).

**Formalization Note.** `A` is `selLaw p a`, `U_r` is `unif r`, `A^i` and `U_r^i` are `prodLaw` on
`Fin i → Fin r`, and `|· − ·|` is the published `IsingLTL.BeliefProp.tvDist` (`½ ℓ¹`). The ℓ∞ bound
is stated coordinatewise, `∀ w, |A(w) − U_r(w)| ≤ 2p`, which is `max_w |…| ≤ 2p` on the nonempty
`Fin r`. "The properties in Lemma 4.3" are the hypotheses `Monotone a` and `hA`. -/
theorem lemma_4_5 {ℓ r : ℕ} [NeZero r] (p : ℝ) (hp0 : 0 < p) (hp : p < 1 / 2)
    (a : Fin ℓ → Fin r) (ha : Monotone a)
    (hA : ∀ i : Fin r, |selLaw p a i - 1 / (r : ℝ)| ≤ 2 * p) :
    (∀ w : Fin r, |selLaw p a w - unif r w| ≤ 2 * p) ∧
    ∀ i : ℕ, 1 ≤ i →
      IsingLTL.BeliefProp.tvDist (prodLaw (selLaw p a) i) (prodLaw (unif r) i) ≤ p * r * i := by sorry

end FriedgutCoalition
