-- Prove2me | Theorems.Thm_LipStableCA_theorem_4_12
-- name    : LipStableCA.theorem_4_12
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T20:54:16.379433+00:00
-- url     : https://prove2.me/theorems/287f31c5-e169-442f-b3c8-dd4c19150d87
-- title:
--   Theorem 4.12 — every $(1-\epsilon)$-approximate rule on two bidders has Lipschitz constant $\Omega(m^2/\epsilon)$
-- statement:
--   Let $c_0=1-h_2(1/4)>0$, with $h_2$ the binary entropy function. For every $m\ge 32$ and every $0<\epsilon\le 1/16$, every randomized mechanism for monotone valuations with two bidders, truthful or not, that is $(1-\epsilon)$-approximate and $K$-Lipschitz has
--   $$K\ge\frac{c_0\,m^2}{1152\,\epsilon}.$$
--
--   So the upper bound of Theorem 4.11 is optimal up to a constant factor, even without truthfulness.
--
--   Differences from the source:
--   - encoding: $\Omega(m^2/\epsilon)$ → the printed constant $c_0/1152$ of p.17; reason: it implies the $\Omega(\cdot)$ form
--   - encoding: a fixed randomized mechanism, truthful or not → its allocation laws $P$, any map from valid profiles to laws; reason: only the laws enter; this covers every mechanism
-- source:
--   Afshinmehr, Koutsoupias, Lipschitz Stable Combinatorial Auctions, STOC 2027 submission (manuscript sha256 c5e4c53f…), Theorem 4.12, p.17

import Definitions.Def_LipStableCA_hardProfile
import Definitions.Def_LipStableCA_IsLipschitz

namespace LipStableCA

/-- **Theorem 4.12.** Afshinmehr, Koutsoupias, *Lipschitz Stable Combinatorial Auctions*, STOC 2027 submission (manuscript sha256 c5e4c53f…), p.17. **Formalization Note.** the printed constant `c_0/1152` of p.17: it implies the `Ω(·)` form. its allocation laws `P`, any map from valid profiles to laws: only the laws enter; this covers every mechanism. -/
theorem theorem_4_12 :
    0 < entropyGap ∧ ∀ (m : ℕ), 32 ≤ m → ∀ ϵ : ℝ, 0 < ϵ → ϵ ≤ 1 / 16 →
      ∀ P : Profile 2 m → Alloc 2 m → ℝ, (∀ v, IsProfile v → IsLaw (P v)) → IsApprox P (1 - ϵ) →
        ∀ K : ℝ, IsLipschitz P K → entropyGap * (m : ℝ) ^ 2 / (1152 * ϵ) ≤ K := by sorry

end LipStableCA
