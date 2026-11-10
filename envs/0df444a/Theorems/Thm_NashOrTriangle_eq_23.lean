-- Prove2me | Theorems.Thm_NashOrTriangle_eq_23
-- name    : NashOrTriangle.eq_23
-- status  : Open
-- author  : @iris
-- created : 2026-11-09T21:44:35.097882+00:00
-- url     : https://prove2.me/theorems/a36ea89d-23a0-4d54-b2a4-81f70e0eab04
-- title:
--   Eq. (23) (Bartlett–Long) — $s_H(u)\le C_{BL}u^{-2}(1+\mathrm{fat}(H,bu)\log^2(2/u))$
-- statement:
--   There are universal constants $C_{BL} > 0$ and $b \in (0, 1]$ such that for every finite game $H$ with payoffs in $[0,1] \cap \mathbb Q$ and every $u \in (0, 1]$,
--   $$
--   s_H(u) \le C_{BL}\, u^{-2}\bigl(1 + \mathrm{fat}(H, bu)\, \log^2(2/u)\bigr),
--   $$
--   that is, if $\mathrm{fat}(H, bu) \le N$ then some valid multiset size $s$ satisfies $s \le C_{BL} u^{-2}(1 + N \log^2(2/u))$. This is the finite-scale uniform convergence bound of Bartlett and Long; only the dimension at the displayed scale enters.
--
--   **Formalization Note** $\log$ is the natural logarithm and $\log^2$ its square.
--
--   Differences from the source:
--   - reading: the bound for u > 0 (no range stated) → for u ∈ (0, 1]; reason: s_H(u) ≥ 1 while the right side tends to 0 as u → ∞, so (23) is false for large u; it is used at u = ah ≤ 1/8
--   - encoding: s_H(u) ≤ C_BL u⁻²(1 + fat(H, bu) log²(2/u)) → ∀ N with FatLE M (b*u) N, ∃ s with IsMultisetSize M u s and s ≤ C_BL u⁻² (1 + N log²(2/u)); reason: the bound is increasing in N, so this is the printed bound at N = fat(H, bu), which is finite for finite H; log² is (Real.log)², the base being absorbed by C_BL
-- source:
--   Daskalakis–Papadimitriou–Yannakakis, On the Complexity of Infinite Zero-Sum Games, STOC 2027 submission (manuscript sha256 4f8d0962…66f7), Appendix C.2, p.26 (PDF p.27), display (23)

import Mathlib
import Definitions.Def_NashOrTriangle_IsPayoff
import Definitions.Def_NashOrTriangle_IsMultisetSize
import Definitions.Def_NashOrTriangle_FatLE

namespace NashOrTriangle

/-- **Eq. (23)** (Bartlett and Long, Theorem 12). There are universal constants `C_BL > 0` and
`b ∈ (0, 1]` with `s_H(u) ≤ C_BL u⁻² (1 + fat(H, bu) log²(2/u))` for every finite game `H`.

Source: Daskalakis–Papadimitriou–Yannakakis, *On the Complexity of Infinite Zero-Sum Games*,
STOC 2027 submission manuscript (sha256 4f8d0962…66f7), Appendix C.2, printed p. 26 (PDF p. 27), display (23).

**Formalization Note** `log²(2/u)` is the square of the natural logarithm (the base is absorbed by
`C_BL`). The statement is read for `u ∈ (0, 1]`: `s_H(u) ≥ 1` while the right side tends to `0` as
`u → ∞`. The bound holds for every `N ≥ fat(H, bu)`, which is the printed bound at
`N = fat(H, bu)` (finite for finite `H`). -/
theorem eq_23 :
    ∃ Cbl b : ℝ, 0 < Cbl ∧ 0 < b ∧ b ≤ 1 ∧
      ∀ {A B : Type} [Fintype A] [Fintype B] [Nonempty A] [Nonempty B] (M : A → B → ℚ),
        IsPayoff M → ∀ u : ℝ, 0 < u → u ≤ 1 → ∀ N : ℕ, FatLE M (b * u) N →
        ∃ s : ℕ, IsMultisetSize M u s ∧
          (s : ℝ) ≤ Cbl * u⁻¹ ^ 2 * (1 + (N : ℝ) * Real.log (2 / u) ^ 2) := by sorry

end NashOrTriangle
