-- Prove2me | Theorems.Thm_L1Sparsifiers_Main_proposition_23
-- name    : L1Sparsifiers.Main.proposition_23
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-11T07:06:55.924135+00:00
-- url     : https://prove2.me/theorems/814b0f6a-7962-4119-b8f9-5073924f934c
-- title:
--   Proposition 23 — the reflected-intersection volume $f_K$: barycenter bound, symmetrizer bound, convex superlevel sets
-- statement:
--   Let $K\subseteq\mathbb R^m$ be a convex body and $f_K(z)=\mathrm{Vol}_m(K\cap(2z-K))$, the volume of the intersection of $K$ with its reflection around $z$ (supported on $z\in K$).
--
--   1. **(A)** There exists $z^*\in K$ with $f_K(z^*)\ge2^{-m}\mathrm{Vol}_m(K)$; in fact the barycenter of $K$ lies in $K$ and is a valid choice for $z^*$.
--   2. **(B)** For every $z\in K\cap-K$,
--   $$\mathrm{Vol}_m(K\cap-K)\ge2^{-m}f_K(z).$$
--   3. **(C)** For every $t>0$ the set $\{z\in K:\ f_K(z)\ge t\}$ is convex.
--
--   Part (A) is a form of the Milman–Pajor inequality. Together, (B) and (C) reduce a lower bound on the symmetrizer $K\cap-K$ to finding a point near the origin where $f_K$ is large, which is how Theorem 22 is proved.
--
--   Differences from the source:
--   - encoding: Lebesgue volume Vol (a value in [0,∞]) → (volume ·).toReal; reason: every set measured here is bounded, so its volume is finite and toReal is the same number
--   - encoding: (A) ∃ z* ∈ K with the bound; the barycenter is a valid choice → three conjuncts: ∃ z ∈ K with the bound, barycenter K ∈ K, and the bound at barycenter K; reason: the second sentence asserts that the barycenter is a valid z*, which includes z* ∈ K
-- source:
--   Victor Reis, Thomas Rothvoss, Linear-size ℓ1 sparsifiers, STOC 2027 submission #162 (October 2026; PDF SHA-256 5137e7dee3cd303bd508f90f5f42c955632af5dc2ec978d9ef575bae4ce23710), §5, Proposition 23, pp.12–13

import Mathlib
import Definitions.Def_L1Sparsifiers_Main_ConvexBodyVolumes

namespace L1Sparsifiers.Main

open MeasureTheory

/-- **Proposition 23** (pp.12–13). "Let K ⊆ ℝ^m be a convex body. Let f_K(z) := Vol_m(K ∩ (2z − K))
denote the volume of the intersection of K with its reflection around z, supported on z ∈ K.
(A) There exists z* ∈ K so that f_K(z*) ≥ 2^{−m} Vol_m(K). In fact, the barycenter of K is a valid
choice for z*. (B) For any z ∈ K ∩ −K one has Vol_m(K ∩ −K) ≥ 2^{−m} f_K(z). (C) For any t > 0, the
set {z ∈ K : f_K(z) ≥ t} is convex." -/
theorem proposition_23 {m : ℕ} (K : Set (Fin m → ℝ)) (hK : IsConvexBody K) :
    ((∃ z ∈ K, ((2 : ℝ) ^ m)⁻¹ * (volume K).toReal ≤ reflVol K z) ∧
      barycenter K ∈ K ∧ ((2 : ℝ) ^ m)⁻¹ * (volume K).toReal ≤ reflVol K (barycenter K)) ∧
    (∀ z ∈ K ∩ -K, ((2 : ℝ) ^ m)⁻¹ * reflVol K z ≤ (volume (K ∩ -K)).toReal) ∧
    (∀ t : ℝ, 0 < t → Convex ℝ {z ∈ K | t ≤ reflVol K z}) := by sorry

end L1Sparsifiers.Main
