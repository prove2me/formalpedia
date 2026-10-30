-- Prove2me | Theorems.Thm_LightningNetwork_RateBounds_symExcess_diagonal_minimizer
-- name    : LightningNetwork.RateBounds.symExcess_diagonal_minimizer
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-30T00:53:48.002765+00:00
-- url     : https://prove2.me/theorems/2722b120-ad0b-4020-be69-eda7a47f491e
-- title:
--   Proof of Theorem 2(ii), eq. (21): $G$ has a unique minimizer, it lies on $l_1 = l_2$, and $G(m,m)$ is (21)
-- statement:
--   Let $\alpha > 1$, $B > 0$, $C \in \mathbb R$, and let $G$ be the excess cost above. Then
--
--   1. there is $m > 0$ such that $G(m,m) \le G(l_1,l_2)$ for all $l_1, l_2 > 0$, and every $(l_1,l_2)$ with $l_1, l_2 > 0$ and $G(l_1,l_2) = G(m,m)$ equals $(m,m)$: the minimizer over the open quadrant exists, is unique, and has $l_1 = l_2$;
--   2. on the diagonal, for every $m > 0$,
--   $$
--   G(m,m) = 2m + \frac{2B\alpha^m}{(\alpha^m-1)^2} - \frac{2C\alpha}{(\alpha-1)^2}. \tag{21}
--   $$
--
--   It therefore suffices to minimize (21) over $m > 0$.
--
--   Differences from the source:
--   - reading: the minimizer must be unique … the minimum must be achieved for l1 = l2 → a minimizer over the open quadrant exists, it is unique, and it lies on the diagonal; reason: the page presupposes that the minimum is attained; the existence is stated explicitly, which is not weaker
--   - encoding: α = α₊ at λ1 = λ2 = λ, with λ, r > 0 → α is a real parameter with α > 1; reason: α₊ + 1/α₊ = 2 + r/λ, so r/λ ↦ α₊ is a bijection of (0, ∞) onto (1, ∞); the instances are the same
--   - generalization: C > 0 (the cost of an on-chain transaction) → C any real number; reason: C enters G only as an additive constant
-- source:
--   Guasoni, Huberman, Shikhelman, Lightning Network Economics: Channels, Management Science (2023), doi:10.1287/mnsc.2022.01664, proof of Theorem 2(ii), eq. (21), p. 11

import Mathlib
import Definitions.Def_LightningNetwork_RateBounds_symExcess

namespace LightningNetwork.RateBounds

/-- **Proof of Theorem 2(ii), unnumbered step and display (21): the minimizer is unique and
diagonal.**
Guasoni, Huberman, Shikhelman, *Lightning Network Economics: Channels*, Management Science (2023),
doi:10.1287/mnsc.2022.01664, proof of Theorem 2(ii), eq. (21), p. 11: "Thus, its minimizer must be unique. Because
the function is symmetric in l1 and l2, the minimum must be achieved for l1 = l2, otherwise it
would not be unique (if (l1, l2) were a minimizer, then (l2, l1) would be another minimizer).
Thus, it suffices to minimize the above function for l1 = l2 = m, that is,
2m + 2Bα^m/(α^m − 1)² − 2Cα/(α − 1)²."

For `α > 1`, `B > 0` and any `C`, with `G = symExcess α B C`:
1. there is `m > 0` such that `G(m, m) ≤ G(l1, l2)` for all `l1, l2 > 0`, and every
   `(l1, l2)` with `l1, l2 > 0` and `G(l1, l2) = G(m, m)` is `(m, m)`;
2. on the diagonal, `G(m, m) = 2m + 2Bα^m/(α^m − 1)² − 2Cα/(α − 1)²` for every `m > 0`.

**Formalization Note.** The page presupposes that the minimum over the open quadrant is
attained; clause 1 states the existence together with the uniqueness and the location on the
diagonal. -/
theorem symExcess_diagonal_minimizer (α B C : ℝ) (hα : 1 < α) (hB : 0 < B) :
    (∃ m : ℝ, 0 < m ∧
        (∀ l1 l2 : ℝ, 0 < l1 → 0 < l2 → symExcess α B C (m, m) ≤ symExcess α B C (l1, l2)) ∧
        (∀ l1 l2 : ℝ, 0 < l1 → 0 < l2 →
          symExcess α B C (l1, l2) = symExcess α B C (m, m) → l1 = m ∧ l2 = m)) ∧
      ∀ m : ℝ, 0 < m →
        symExcess α B C (m, m) = 2 * m + 2 * B * α ^ m / (α ^ m - 1) ^ 2
          - 2 * C * α / (α - 1) ^ 2 := by sorry

end LightningNetwork.RateBounds
