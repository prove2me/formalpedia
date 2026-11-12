-- Prove2me | Theorems.Thm_L1Sparsifiers_Main_theorem_22_claim_I
-- name    : L1Sparsifiers.Main.theorem_22_claim_I
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-11T07:07:29.888192+00:00
-- url     : https://prove2.me/theorems/d62256f9-f214-47b3-b337-df25b6ffd2db
-- title:
--   §5, proof of Theorem 22, Claim I — a point $z^*$ with $\|z^*\|_\infty\le r$ and $f_K(z^*)\ge p\,2^{-3m}$
-- statement:
--   Assume the hypotheses of Theorem 22: $p,\varepsilon\in(0,1/2]$, $m\ge1$ an integer with $m\ge\log_2(1/p)/\varepsilon^2$, and $K\subseteq[-1,1]^m$ a convex body with $[-\varepsilon,\varepsilon]^m\subseteq K$ and $\mathrm{Vol}_S(K_S)\ge p\,2^{|S|}$ for every $S\subseteq[m]$. Let
--   $$r=\sqrt{\frac{\log_2(1/p)}{m}},\qquad f_K(z)=\mathrm{Vol}_m\big(K\cap(2z-K)\big).$$
--   Then there is $z^*\in K$ with
--   $$f_K(z^*)\ge p\,2^{-3m}\qquad\text{and}\qquad\|z^*\|_\infty\le r.$$
--
--   Since $r\le\varepsilon$, such a $z^*$ lies in $K\cap-K$, and Proposition 23(B) then yields Theorem 22.
--
--   Differences from the source:
--   - encoding: the hypotheses of Theorem 22 and the abbreviation r, stated in the surrounding proof → copied into the binders; r and f_K written out; reason: a claim inside a proof inherits the proof's assumptions
--   - encoding: Lebesgue volume Vol (a value in [0,∞]) → (volume ·).toReal; reason: every set measured here is bounded, so its volume is finite and toReal is the same number
-- source:
--   Victor Reis, Thomas Rothvoss, Linear-size ℓ1 sparsifiers, STOC 2027 submission #162 (October 2026; PDF SHA-256 5137e7dee3cd303bd508f90f5f42c955632af5dc2ec978d9ef575bae4ce23710), §5, proof of Theorem 22, Claim I, p.15 (hypotheses: Theorem 22, p.12)

import Mathlib
import Definitions.Def_L1Sparsifiers_Main_UniformCube
import Definitions.Def_L1Sparsifiers_Main_ConvexBodyVolumes

namespace L1Sparsifiers.Main

open MeasureTheory

/-- **Claim I in the proof of Theorem 22** (p.15). Under the hypotheses of Theorem 22 (p.12):
`p, ε ∈ (0, 1/2]`, `m ≥ 1` with `m ≥ log₂(1/p)/ε²`, `K ⊆ [−1,1]^m` a convex body with
`[−ε,ε]^m ⊆ K` and `Vol_S(K_S) ≥ p 2^{|S|}` for every `S ⊆ [m]`; with `r := √(log₂(1/p)/m)` and
`f_K(z) = Vol_m(K ∩ (2z − K))`:
"Claim I. There is a z* ∈ K with f_K(z*) ≥ p 2^{−3m} and ‖z*‖_∞ ≤ r." -/
theorem theorem_22_claim_I {m : ℕ} (hm : 0 < m) (p ε : ℝ) (hp0 : 0 < p) (hp : p ≤ 1 / 2)
    (hε0 : 0 < ε) (hε : ε ≤ 1 / 2) (hmε : Real.logb 2 (1 / p) / ε ^ 2 ≤ m)
    (K : Set (Fin m → ℝ)) (hK : IsConvexBody K) (hKcube : K ⊆ cube m)
    (hεK : Set.Icc (fun _ => -ε) (fun _ => ε) ⊆ K)
    (hsec : ∀ S : Finset (Fin m), p * 2 ^ S.card ≤ (volume (coordSection K S)).toReal) :
    ∃ z ∈ K, p * ((2 : ℝ) ^ (3 * m))⁻¹ ≤ reflVol K z ∧
      ∀ i, |z i| ≤ Real.sqrt (Real.logb 2 (1 / p) / m) := by sorry

end L1Sparsifiers.Main
