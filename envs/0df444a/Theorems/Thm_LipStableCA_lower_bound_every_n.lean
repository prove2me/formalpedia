-- Prove2me | Theorems.Thm_LipStableCA_lower_bound_every_n
-- name    : LipStableCA.lower_bound_every_n
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T20:54:31.012876+00:00
-- url     : https://prove2.me/theorems/e615a5ec-f443-4e59-b6e0-b30fdc197b0c
-- title:
--   §4 opening — the lower bound for every number $n\ge 2$ of bidders (lower-bound half of the $\Theta$)
-- statement:
--   For every number $n\ge 2$ of bidders, every $m\ge 32$ and $0<\epsilon\le 1/16$, a $(1-\epsilon)$-approximate and $K$-Lipschitz allocation rule for monotone valuations has
--   $$K\ge\frac{c_0\,m^2}{1152\,\epsilon}.$$
--
--   This is the lower-bound half of the statement opening §4, that the optimal Lipschitz constant is $\Theta(m^2/\epsilon)$ for every $n\ge 2$; the upper-bound half is Theorem 4.11. The step from two bidders is to give zero valuations to bidders $3,\dots,n$ and to project the laws to bidders 1 and 2.
--
--   Differences from the source:
--   - encoding: $\Omega(m^2/\epsilon)$ inside the printed $\Theta(m^2/\epsilon)$ → the explicit constant $c_0/1152$ of Theorem 4.12; reason: padding with zero bidders preserves the constant
--   - reading: the sentence opening §4 also claims attainment by a TIE and ex-post IR mechanism → only the lower bound is stated here; attainment is Theorem 4.11; reason: the sentence's upper half is exactly Theorem 4.11, which is a separate milestone and part of the goal
--   - encoding: a fixed randomized mechanism, truthful or not → its allocation laws $P$, any map from valid profiles to laws; reason: only the laws enter; this covers every mechanism
-- source:
--   Afshinmehr, Koutsoupias, Lipschitz Stable Combinatorial Auctions, STOC 2027 submission (manuscript sha256 c5e4c53f…), §4 opening, p.14

import Definitions.Def_LipStableCA_hardProfile
import Definitions.Def_LipStableCA_IsLipschitz

namespace LipStableCA

/-- **§4 opening.** Afshinmehr, Koutsoupias, *Lipschitz Stable Combinatorial Auctions*, STOC 2027 submission (manuscript sha256 c5e4c53f…), p.14. **Formalization Note.** the explicit constant `c_0/1152` of Theorem 4.12: padding with zero bidders preserves the constant. only the lower bound is stated here; attainment is Theorem 4.11: the sentence's upper half is exactly Theorem 4.11, which is a separate milestone and part of the goal. its allocation laws `P`, any map from valid profiles to laws: only the laws enter; this covers every mechanism. -/
theorem lower_bound_every_n (n m : ℕ) (hn : 2 ≤ n) (hm : 32 ≤ m) (ϵ : ℝ) (h0 : 0 < ϵ) (h1 : ϵ ≤ 1 / 16)
    (P : Profile n m → Alloc n m → ℝ) (hP : ∀ v, IsProfile v → IsLaw (P v)) (happ : IsApprox P (1 - ϵ))
    (K : ℝ) (hK : IsLipschitz P K) : entropyGap * (m : ℝ) ^ 2 / (1152 * ϵ) ≤ K := by sorry

end LipStableCA
