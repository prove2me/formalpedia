-- Prove2me | Theorems.Thm_FriedgutCoalition_claim_4_2
-- name    : FriedgutCoalition.claim_4_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T21:35:34.857123+00:00
-- url     : https://prove2.me/theorems/40e5c8bb-3900-4d33-a345-e8552ccda2b3
-- title:
--   Claim 4.2 — the encoded function's $p$-biased influence is at most $2\,\mathbf J^0(f,\mathbf A)$
-- statement:
--   Let $f:[r]^n\to\{0,1\}$ be monotone and $p\in(0,1/2)$ (the standing assumptions of §4). Fix any nondecreasing $a\in[r]^\ell$, let $g:\{0,1\}^{\ell n}\to\{0,1\}$ be the encoded function of eq. (1), and let $\mathbf A$ be the law of $\phi_a(y)$ for $y\sim\mu_p^\ell$. Then
--
--   $$\mathbf I^p(g)\le2\cdot\mathbf J^0(f,\mathbf A).$$
--
--   This is the influence half of Lemma 3.5: because every nonconstant threshold of $\phi_a$ is an OR of encoding bits, resampling a bit changes $g$ only as often as coordinate influence towards $0$ allows.
--
--   Differences from the source:
--   - encoding: r ∈ ℕ with the value 1 ∈ [r] used (Definition 4.1) → [NeZero r], i.e. r ≥ 1; reason: [r] must be nonempty for ϕ_a(0^ℓ) = 1 and for 1/r; the source's r is the alphabet size of f : [r]ⁿ → {0,1}
--   - encoding: g : {0,1}^m → {0,1} with m = ℓ·n, blocks of consecutive bits → encodeFn a f on Fin n × Fin ℓ → Bool, block j = {j} × Fin ℓ; reason: a relabelling of the m bits that keeps each block and its order; total influence is invariant under relabelling
--   - encoding: {0,1}, [n], [r] = {1,…,r} → Bool (false < true), Fin n, Fin r (the value 1 of [r] is 0 : Fin r, the value r is its top); reason: Lean conventions; the same instances
-- source:
--   Chattopadhyay, Gurumukhani, A Resolution of Friedgut's Conjecture on Influential Coalitions, arXiv:2609.16401 (held file sha256 51f298ff…), Claim 4.2, p.11 (with Definition 4.1 and eq. (1); standing assumptions of §4, p.10)

import Mathlib
import Definitions.Def_FriedgutCoalition_coalProb
import Definitions.Def_FriedgutCoalition_pInfl
import Definitions.Def_FriedgutCoalition_maxSel

namespace FriedgutCoalition

/-- **Claim 4.2** (Chattopadhyay–Gurumukhani, arXiv:2609.16401 (held file sha256 51f298ff…), p.11). Let `f : [r]ⁿ → {0,1}` be monotone and
`p ∈ (0, 1/2)` (§4's standing assumptions, p.10). For any nondecreasing `a ∈ [r]^ℓ`, the encoded
function `g` of eq. (1) satisfies `I^p(g) ≤ 2 · J⁰(f, A)`, where `A` is the law of `ϕ_a(y)` for
`y ∼ µ^ℓ_p`.

**Formalization Note.** `[r]` is `Fin r` with `r ≥ 1` (`[NeZero r]`; Definition 4.1 outputs the value
`1 ∈ [r]`). The `m = ℓn` bits of `g` are indexed by `Fin n × Fin ℓ`, block `j` being `{j} × Fin ℓ`.
`A` is `selLaw p a`, and `J⁰(f, A)` is `totalToward (selLaw p a) f false`. -/
theorem claim_4_2 {n ℓ r : ℕ} [NeZero r] (p : ℝ) (hp0 : 0 < p) (hp : p < 1 / 2)
    (f : (Fin n → Fin r) → Bool) (hf : Monotone f) (a : Fin ℓ → Fin r) (ha : Monotone a) :
    totalPInfl p (encodeFn a f) ≤ 2 * totalToward (selLaw p a) f false := by sorry

end FriedgutCoalition
