-- Prove2me | Theorems.Thm_KTCenter_lemma_5_5
-- name    : KTCenter.lemma_5_5
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T11:30:41.268022+00:00
-- url     : https://prove2.me/theorems/7d7aeae0-1579-444f-b123-6055dfcdb170
-- title:
--   Lemma 5.5 — $0\le\tilde C_i(p)\le\mathcal K(\sigma_p,\pi_i)\le\tilde C_i(p)+\zeta W$
-- statement:
--   Let $(w_v)$ be nonnegative integers, $0<\beta<1$, $0<\zeta<1$, and let $\tilde C_i$ be the surrogate cost produced by Algorithms 2 and 3 for the input ranking $\pi_i$. For every allowed assignment $p$,
--
--   $$0\le\tilde C_i(p)\le\mathcal K(\sigma_p,\pi_i)\le\tilde C_i(p)+\zeta W.\qquad(26)$$
--
--   The surrogate cost, which couples keys only inside blocks, thus tracks the true distance within $\zeta W$.
--
--   Differences from the source:
--
--   - generalization: allowances of the fixed tuple and an input π_i → arbitrary nonnegative integer allowances and an arbitrary ranking π_i; reason: the construction and proof use nothing else; it specializes to the source
--   - encoding: assignment on U extended by p_v = v → full key vector in ∏ P_v; reason: P_v = {v} when w_v = 0
--   - encoding: 0 ≤ C̃_i(p) → holds by the type ℕ, kept as a conjunct; reason: Lean convention
-- source:
--   Chakraborty, Das, Mukherjee, Kendall–tau Center Admits a PTAS, STOC 2027 submission (manuscript sha256 4739ffba…), Lemma 5.5, eq. (26), p.32 (PDF p.34)

import Mathlib
import Definitions.Def_KTCenter_KeyDomains
import Definitions.Def_KTCenter_PartitionCosts

namespace KTCenter

/-- **Lemma 5.5** (Approximation of the input distances), eq. (26), p.32 (PDF p.34).

Chakraborty, Das, Mukherjee, *Kendall–tau Center Admits a PTAS*, STOC 2027 submission (manuscript
sha256 4739ffba…).

**Formalization Note.** Algorithms 2 and 3 for any allowances `w` and any ranking `ρ = πᵢ`. A surrogate
cost is a natural number, so the printed `0 ≤ C̃ᵢ(p)` holds by type; it is kept as written. -/
theorem lemma_5_5 {d : ℕ} (w : Fin d → ℕ) (β ζ : ℚ) (hβ0 : 0 < β) (hβ1 : β < 1) (hζ0 : 0 < ζ)
    (hζ1 : ζ < 1) (p : Fin d → ℚ) (hp : p ∈ assignments w β) (ρ : Equiv.Perm (Fin d)) :
    0 ≤ PartitionCosts.surrogate w β ζ ρ p ∧
      PartitionCosts.surrogate w β ζ ρ p ≤ dist (sortRanking p) ρ ∧
      (dist (sortRanking p) ρ : ℚ) ≤
        (PartitionCosts.surrogate w β ζ ρ p : ℚ) + ζ * (totalW w : ℚ) := by sorry

end KTCenter
