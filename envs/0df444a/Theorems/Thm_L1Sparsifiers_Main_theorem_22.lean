-- Prove2me | Theorems.Thm_L1Sparsifiers_Main_theorem_22
-- name    : L1Sparsifiers.Main.theorem_22
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-11T07:07:15.266185+00:00
-- url     : https://prove2.me/theorems/bc1ad647-d6a0-4d62-927d-7c716399668c
-- title:
--   Theorem 22 — the symmetrizer bound $\mathrm{Vol}_m(K\cap-K)\ge2^{-5m}$
-- statement:
--   Let $p,\varepsilon\in(0,1/2]$ and let $m$ be a positive integer with
--   $$m\ge\frac{\log_2(1/p)}{\varepsilon^2}.$$
--   Let $K\subseteq[-1,1]^m$ be a convex body with $[-\varepsilon,\varepsilon]^m\subseteq K$ and
--   $$\mathrm{Vol}_S(K_S)\ge p\,2^{|S|}\qquad\text{for every }S\subseteq[m].$$
--   Then
--   $$\mathrm{Vol}_m(K\cap-K)\ge2^{-5m}.$$
--
--   $K$ is not assumed symmetric: a body that is far from symmetric still has an exponentially large symmetrizer as soon as all its coordinate sections are large. With Corollary 21 this gives Corollary 25.
--
--   Differences from the source:
--   - encoding: Lebesgue volume Vol (a value in [0,∞]) → (volume ·).toReal; reason: every set measured here is bounded, so its volume is finite and toReal is the same number
-- source:
--   Victor Reis, Thomas Rothvoss, Linear-size ℓ1 sparsifiers, STOC 2027 submission #162 (October 2026; PDF SHA-256 5137e7dee3cd303bd508f90f5f42c955632af5dc2ec978d9ef575bae4ce23710), §5, Theorem 22, p.12

import Mathlib
import Definitions.Def_L1Sparsifiers_Main_UniformCube
import Definitions.Def_L1Sparsifiers_Main_ConvexBodyVolumes

namespace L1Sparsifiers.Main

open MeasureTheory

/-- **Theorem 22** (p.12). "Let p, ε ∈ (0, 1/2] and m be a positive integer so that
m ≥ log₂(1/p)/ε². Let K ⊆ [−1,1]^m be a convex body so that [−ε,ε]^m ⊆ K and, for every S ⊆ [m],
Vol_S(K_S) ≥ p 2^{|S|}. Then Vol_m(K ∩ −K) ≥ 2^{−5m}." -/
theorem theorem_22 {m : ℕ} (hm : 0 < m) (p ε : ℝ) (hp0 : 0 < p) (hp : p ≤ 1 / 2)
    (hε0 : 0 < ε) (hε : ε ≤ 1 / 2) (hmε : Real.logb 2 (1 / p) / ε ^ 2 ≤ m)
    (K : Set (Fin m → ℝ)) (hK : IsConvexBody K) (hKcube : K ⊆ cube m)
    (hεK : Set.Icc (fun _ => -ε) (fun _ => ε) ⊆ K)
    (hsec : ∀ S : Finset (Fin m), p * 2 ^ S.card ≤ (volume (coordSection K S)).toReal) :
    ((2 : ℝ) ^ (5 * m))⁻¹ ≤ (volume (K ∩ -K)).toReal := by sorry

end L1Sparsifiers.Main
