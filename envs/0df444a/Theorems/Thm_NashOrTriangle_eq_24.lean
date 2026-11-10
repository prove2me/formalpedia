-- Prove2me | Theorems.Thm_NashOrTriangle_eq_24
-- name    : NashOrTriangle.eq_24
-- status  : Open
-- author  : @iris
-- created : 2026-11-09T21:46:34.200822+00:00
-- url     : https://prove2.me/theorems/988a4a3a-7059-463b-ae4b-33cf7e881bf6
-- title:
--   Eq. (24) — no $(t,\gamma)$-triangle and $bu\ge2\gamma$ ⇒ $s_H(u)=O(tu^{-3}\log^2(2/u))$
-- statement:
--   Let $C_{BL} > 0$ and $b \in (0, 1]$ be constants for which the Bartlett–Long bound (23) holds. Then there is a constant $C$ such that for every finite game $H$ with payoffs in $[0,1] \cap \mathbb Q$ and no $(t, \gamma)$-triangle, and every $u \in (0, 1]$ with $bu \ge 2\gamma$,
--   $$
--   s_H(u) \le C\, t\, u^{-3} \log^2(2/u),
--   $$
--   that is, $s_H(u) = O\bigl(t u^{-3} \log^2(2/u)\bigr)$. With $u = ah$ and $h = 1/(4k)$ this gives $s_H(ah) = O(tk^3 \log^2 k)$ in the proof of Theorem 2.1(b).
--
--   Differences from the source:
--   - reading: b, the constant of (23) → any (C_BL, b) with C_BL > 0, b ∈ (0, 1] satisfying (23), given as a hypothesis; C may depend on C_BL and b; reason: (24) is derived from (23) with its b, and C_BL, b are universal, so C is universal
--   - reading: the bound for u > 0 (no range stated) → for u ∈ (0, 1]; reason: as for (23): s_H(u) ≥ 1 while the right side tends to 0 as u → ∞
--   - encoding: s_H(u) = O(t u⁻³ log²(2/u)) → ∃ C, ∃ s with IsMultisetSize M u s and s ≤ C t u⁻³ (Real.log (2/u))²; reason: big-O with a constant uniform in t, γ, H and u
-- source:
--   Daskalakis–Papadimitriou–Yannakakis, On the Complexity of Infinite Zero-Sum Games, STOC 2027 submission (manuscript sha256 4f8d0962…66f7), Appendix C.2, p.26 (PDF p.27), display (24)

import Mathlib
import Definitions.Def_NashOrTriangle_IsPayoff
import Definitions.Def_NashOrTriangle_IsMultisetSize
import Definitions.Def_NashOrTriangle_FatLE
import Definitions.Def_NashOrTriangle_HasMarginTriangle

namespace NashOrTriangle

/-- **Eq. (24).** Let `C_BL > 0` and `b ∈ (0, 1]` be constants for which (23) holds. Combined with
Lemma C.4: there is `C` such that if a finite game `H` has no `(t, γ)`-triangle and `bu ≥ 2γ`, then
`s_H(u) ≤ C t u⁻³ log²(2/u)`, i.e. `s_H(u) = O(t u⁻³ log²(2/u))`.

Source: Daskalakis–Papadimitriou–Yannakakis, *On the Complexity of Infinite Zero-Sum Games*,
STOC 2027 submission manuscript (sha256 4f8d0962…66f7), Appendix C.2, printed p. 26 (PDF p. 27), display (24).

**Formalization Note** The `b` of (24) is the `b` of (23), so the statement is quantified over any
pair `(C_BL, b)` satisfying (23) (whose existence is Eq. (23)); `C` may depend on `C_BL` and `b`,
which are universal. `u ∈ (0, 1]` as in (23). -/
theorem eq_24 (Cbl b : ℝ) (hC : 0 < Cbl) (hb0 : 0 < b) (hb1 : b ≤ 1)
    (h23 : ∀ {A B : Type} [Fintype A] [Fintype B] [Nonempty A] [Nonempty B] (M : A → B → ℚ),
      IsPayoff M → ∀ u : ℝ, 0 < u → u ≤ 1 → ∀ N : ℕ, FatLE M (b * u) N →
      ∃ s : ℕ, IsMultisetSize M u s ∧
        (s : ℝ) ≤ Cbl * u⁻¹ ^ 2 * (1 + (N : ℝ) * Real.log (2 / u) ^ 2)) :
    ∃ C : ℝ, ∀ {A B : Type} [Fintype A] [Fintype B] [Nonempty A] [Nonempty B] (M : A → B → ℚ),
      IsPayoff M → ∀ (t : ℕ) (γ : ℝ), ¬ HasMarginTriangle M t γ →
      ∀ u : ℝ, 0 < u → u ≤ 1 → 2 * γ ≤ b * u →
        ∃ s : ℕ, IsMultisetSize M u s ∧
          (s : ℝ) ≤ C * (t : ℝ) * u⁻¹ ^ 3 * Real.log (2 / u) ^ 2 := by sorry

end NashOrTriangle
