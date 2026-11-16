-- Prove2me | Theorems.Thm_KhintchineTwoRegime_Supplement_theorem_3
-- name    : KhintchineTwoRegime.Supplement.theorem_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T04:26:11.052089+00:00
-- url     : https://prove2.me/theorems/19478adc-9977-46e3-a9fc-94ccde1ebe1c
-- title:
--   Theorem 3 — linear Khintchine inequality $K_n(\omega)\ge1/\sqrt2+\tau(\omega)/20$ for every unit vector
-- statement:
--   Let $\varepsilon_1,\dots,\varepsilon_n$ be independent Rademacher signs and $K_n(\omega)=\mathbb E\bigl|\sum_i\omega_i\varepsilon_i\bigr|$. For $\omega\in\mathbb R^n$ let $\tau(\omega)=\min_{1\le i<j\le n}\|\omega\pm e_i/\sqrt2\pm e_j/\sqrt2\|_2$ be its Euclidean distance to the extremal set (eq. (5), all sign choices).
--
--   **Theorem 3 (Improved linear Khintchine inequality).** For every $n\ge2$ and every unit vector $\omega\in\mathbb R^n$ ($\|\omega\|_2=1$),
--   $$
--   K_n(\omega)\ge\frac1{\sqrt2}+\frac1{20}\,\tau(\omega).
--   $$
--
--   Szarek's sharp inequality $K_n(\omega)\ge1/\sqrt2$ is attained exactly on the extremal set; this is a dimension-free robust version, with the explicit slope $1/20$: the excess of $K_n$ over the sharp constant grows at least linearly in the distance to the equality cases.
--
--   **Formalization Note** $\tau$ is eq. (5) itself; it is invariant under signs and permutations and equals $\|\omega'-\omega^*\|_2$ for the proper rearrangement $\omega'$ of $\omega$, which is the paper's "after making $\omega$ proper by signs and permutations". $K_n$ is the published `KhintchineTwoRegime.K` and $\|\cdot\|_2$ the published `l2Norm`.
--
--   Differences from the source:
--
--   - encoding: τ(ω) "defined in (5), after making ω proper by signs and permutations" → eq. (5) applied to ω directly (the minimum over i < j and all signs); reason: (5) is invariant under signs and permutations, so it takes the same value at ω and at its proper rearrangement
--   - encoding: the standing assumption n ≥ 2 of (5) → an argument hn : 2 ≤ n of tau; reason: the minimum in (5) is over a nonempty set only when n ≥ 2, and the theorem assumes n ≥ 2
-- source:
--   Fang–Wang, A Two-regime Khintchine Inequality and an Improved Bound on the Degree-1 Fourier Weight for Linear Threshold Functions, arXiv:2608.27908v2 (held version of 2026-11-02, sha256 1d8d9bf1…), Theorem 3, eq. (17), p.9 (τ from §2, eq. (5), p.4)

import Mathlib
import Definitions.Def_HighDimProb_SparseRecovery_L2Norm
import Definitions.Def_KhintchineTwoRegime_K
import Definitions.Def_KhintchineTwoRegime_Supplement_tau
open HighDimProb.SparseRecovery (l2Norm)

namespace KhintchineTwoRegime.Supplement

/-- Theorem 3 (Improved linear Khintchine inequality) (Fang–Wang, *A Two-regime Khintchine Inequality and an Improved Bound on the Degree-1 Fourier Weight for Linear Threshold Functions*, arXiv:2608.27908v2 (held version of 2026-11-02, sha256 1d8d9bf1…), Theorem 3, eq. (17), p.9):
for every `n ≥ 2` and every unit vector `ω ∈ ℝⁿ`,
`Kₙ(ω) ≥ 1/√2 + (1/20) τ(ω)`, where `τ(ω)` is the distance to the extremal set (5).

**Formalization Note** `‖ω‖₂ = 1` is `l2Norm ω = 1` (Euclidean). `τ` is eq. (5) itself
(`tau`), a minimum over all pairs `i < j` and all signs; it is invariant under signs and
permutations and equals `‖ω' − ω*‖₂` for the proper rearrangement `ω'` of `ω`, so the
paper's clause "after making ω proper" needs no separate encoding. No properness hypothesis. -/
theorem theorem_3 (n : ℕ) (hn : 2 ≤ n) (ω : Fin n → ℝ) (hω : l2Norm ω = 1) :
    1 / Real.sqrt 2 + 1 / 20 * tau hn ω ≤ KhintchineTwoRegime.K n ω := by sorry

end KhintchineTwoRegime.Supplement
