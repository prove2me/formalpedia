-- Prove2me | Theorems.Thm_HorodeckiBoundKey_corner_norm_near_half
-- name    : HorodeckiBoundKey.corner_norm_near_half
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T03:15:31.936699+00:00
-- url     : https://prove2.me/theorems/67fa1d3b-f8a7-4f80-8f78-8c4017f970e5
-- title:
--   For $p>1/4$ the value of (13) gets arbitrarily close to $1/2$
-- statement:
--   Let $f(p,l,n)$ be the right-hand side of (13). If $\frac14<p\le\frac12$, then for every $\varepsilon>0$ there is $n_0$ such that for every $n\ge n_0$ there is $l_0$ with
--   $$
--   f(p,l,n) > \tfrac12-\varepsilon\qquad\text{for all } l\ge l_0 .
--   $$
--
--   So for $p>1/4$ the off-diagonal block of $\rho'$ can be made as close to that of a private bit as desired, by taking many copies $n$ and, for that $n$, long hiding states $l$.
--
--   **Formalization Note** The order of choice is $n$ first, then $l$; see the differences below.
--
--   Differences from the source:
--   - reading: "if we had previously taken l large enough, and now take large n" → ∀ε>0 ∃n₀ ∀n≥n₀ ∃l₀ ∀l≥l₀, f(p,l,n) > 1/2 − ε; reason: the literal order (l fixed, then n → ∞) is false since (1 − 2^{-l})^n → 0; with n chosen first, letting l → ∞ gives 1/(2(1 + ((1−2p)/(2p))^n)), which tends to 1/2 exactly when p > 1/4; this is the only true order
--   - encoding: p > 1/4 (for the state (11), so p ≤ 1/2) → 1/4 < p ≤ 1/2; reason: (11) is a state only for p ≤ 1/2; the upper bound excludes no value at which the sentence is about a state
-- source:
--   Horodecki, Horodecki, Horodecki, Oppenheim, Secure key from bound entanglement, arXiv:quant-ph/0309110v2, p.3, after eq. (13) ("Now, for p > 1/4 the norm can be arbitrarily close to 1/2 if we had previously taken l large enough, and now take large n.")

import Mathlib
import Definitions.Def_HorodeckiBoundKey_cornerNormValue

namespace HorodeckiBoundKey

/-- Horodecki, Horodecki, Horodecki, Oppenheim, arXiv:quant-ph/0309110v2, p.3, after (13): "Now,
for p > 1/4 the norm can be arbitrarily close to 1/2 if we had previously taken l large enough,
and now take large n."

For `1/4 < p ≤ 1/2` and every `ε > 0` there is `n₀` such that for every `n ≥ n₀` there is `l₀`
with `f(p, l, n) > 1/2 − ε` for every `l ≥ l₀`, where `f` is the right-hand side of (13)
(`cornerNormValue`).

**Formalization Note.** The quantifier order is `n` first, then `l`. For fixed `l` the value
tends to `0` as `n → ∞` (the factor `(1 − 2^{-l})ⁿ`), so the literal order "`l` first, then
large `n`" is false; the order stated is the one under which the sentence is true (for each
`n`, letting `l → ∞` gives `½ / (1 + ((1−2p)/(2p))ⁿ)`, which tends to `½` since
`(1−2p)/(2p) < 1` exactly when `p > 1/4`). -/
theorem corner_norm_near_half (p : ℝ) (hp : 1 / 4 < p) (hp' : p ≤ 1 / 2) (ε : ℝ) (hε : 0 < ε) :
    ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n → ∃ l₀ : ℕ, ∀ l : ℕ, l₀ ≤ l →
      1 / 2 - ε < cornerNormValue p l n := by sorry

end HorodeckiBoundKey
