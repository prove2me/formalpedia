-- Prove2me | Theorems.Thm_MomentSearch_opt_le_of_peak
-- name    : MomentSearch.opt_le_of_peak
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T04:11:22.4371+00:00
-- url     : https://prove2.me/theorems/812d8730-18ab-48ef-afce-ebaec7fc342b
-- title:
--   Proof of Theorem 16 — $\mathrm{OPT}(p)\le 1+\gamma\lceil\log_2 n\rceil = O(1)$ for a peaked distribution
-- statement:
--   Let $n\ge2$, let $p\in\Delta_n$, $m\in[n]_0$ and $\gamma\in\mathbb R$ with $p_m\ge1-\gamma$. Then
--
--   $$
--   \mathrm{OPT}(p)\ \le\ 1+\gamma\,\lceil\log_2 n\rceil ,
--   $$
--
--   and if moreover $\gamma\le 1/(4\log_2 n)$ (the bound obtained in the proof of Theorem 16), then $\mathrm{OPT}(p)\le 3/2$.
--
--   A searcher who knows $p$ first queries the peak $m$ and otherwise finishes with binary search, so a distribution concentrated at one point has constant optimal cost.
--
--   Differences from the source:
--   - generalization: the proof's distributions p⁽ʳ⁾ with peak m_r → every distribution p ∈ Δ_n, every m and γ with p_m ≥ 1 − γ; reason: the proof's p⁽ʳ⁾ satisfy p⁽ʳ⁾_{m_r} ≥ 1 − γ, so the statement specializes to the page
--   - generalization: = O(1) (under the proof's γ ≤ 1/(4 log n)) → OPT(p) ≤ 3/2 whenever γ ≤ 1/(4 log₂ n); reason: an explicit constant implies O(1); 1 + γ⌈log₂ n⌉ ≤ 1 + 2 log₂ n /(4 log₂ n) for n ≥ 2
--   - encoding: ⌈log₂ n⌉ → Nat.clog 2 n; reason: equal for n ≥ 1
-- source:
--   Megow, Stein, Verschae, Distributionally Robust Search: The Power of Information and the Limits of Moments, arXiv:2611.04559 (held version, sha256 fbfa4b43…), App. C.3, proof of Theorem 16, p.27 (PDF p.29)

import Mathlib
import Definitions.Def_MomentSearch_OPT

namespace MomentSearch

/-- **The optimal cost of a peaked distribution**, the display in the proof of Theorem 16, Megow, Stein, Verschae, *Distributionally Robust Search: The Power of Information and the Limits of Moments*, arXiv:2611.04559 (held version, sha256 fbfa4b43…),
App. C.3, p.27 (PDF p.29).

If `p` is a distribution on `[n]₀` (`n ≥ 2`) and `p_m ≥ 1 − γ`, then querying `m` first and
finishing with binary search shows `OPT(p) ≤ 1 + γ ⌈log₂ n⌉`; and when `γ ≤ 1/(4 log₂ n)`, as in
the proof, this is `O(1)`: `OPT(p) ≤ 3/2`.

**Formalization Note.** `⌈log₂ n⌉` is `Nat.clog 2 n` (equal for `n ≥ 1`). Stated for every
distribution and peak; the paper's display is about its `p⁽ʳ⁾` and `m_r`. The `O(1)` is made
explicit as the constant `3/2` under the proof's bound `γ ≤ 1/(4 log₂ n)`. -/
theorem opt_le_of_peak {n : ℕ} (hn : 2 ≤ n) (p : Fin n → ℝ) (hp : p ∈ stdSimplex ℝ (Fin n))
    (m : Fin n) (γ : ℝ) (hγ : 1 - γ ≤ p m) :
    OPT p ≤ 1 + γ * (Nat.clog 2 n : ℝ) ∧
    (γ ≤ 1 / (4 * Real.logb 2 n) → OPT p ≤ 3 / 2) := by sorry

end MomentSearch
