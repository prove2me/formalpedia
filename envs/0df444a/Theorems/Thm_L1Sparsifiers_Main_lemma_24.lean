-- Prove2me | Theorems.Thm_L1Sparsifiers_Main_lemma_24
-- name    : L1Sparsifiers.Main.lemma_24
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-11T07:07:31.237073+00:00
-- url     : https://prove2.me/theorems/4260eac6-8450-4b7f-9885-e4f62c5c4c53
-- title:
--   Lemma 24 — a halfspace cut $K_a$ keeps volume $\ge p\,2^{-2m}$
-- statement:
--   Let $m\ge1$, $p\in(0,1/2]$ and $\lambda=\sqrt{\log_2(1/p)}$ (so $\lambda\ge1$). Let $K\subseteq[-1,1]^m$ be a convex body with $0\in K$ and
--   $$\mathrm{Vol}_S(K_S)\ge p\,2^{|S|}\qquad\text{for every }S\subseteq[m].$$
--   Then for every $a\in\mathbb R^m$ the set
--   $$K_a=K\cap\Big\{x\in[-1,1]^m:\ \langle a,x\rangle\le\frac{\lambda}{\sqrt m}\,\|a\|_1\Big\}$$
--   has volume $\mathrm{Vol}_m(K_a)\ge p\,2^{-2m}$.
--
--   This is the key technical estimate in the proof of Theorem 22: no halfspace through a slightly shifted origin can cut away almost all of $K$.
--
--   Differences from the source:
--   - encoding: m (the dimension; λ/√m appears in the statement) → hypothesis 0 < m; reason: λ/√m is undefined at m = 0; the hypothesis excludes exactly that case
--   - encoding: λ = √(log₂(1/p)) ≥ 1 → λ written out as Real.sqrt (Real.logb 2 (1/p)); λ ≥ 1 is not a hypothesis; reason: λ ≥ 1 follows from p ≤ 1/2
--   - encoding: Lebesgue volume Vol (a value in [0,∞]) → (volume ·).toReal; reason: every set measured here is bounded, so its volume is finite and toReal is the same number
-- source:
--   Victor Reis, Thomas Rothvoss, Linear-size ℓ1 sparsifiers, STOC 2027 submission #162 (October 2026; PDF SHA-256 5137e7dee3cd303bd508f90f5f42c955632af5dc2ec978d9ef575bae4ce23710), §5, Lemma 24, p.13

import Mathlib
import Definitions.Def_L1Sparsifiers_Main_UniformCube
import Definitions.Def_L1Sparsifiers_Main_ConvexBodyVolumes

namespace L1Sparsifiers.Main

open MeasureTheory

/-- **Lemma 24** (p.13). "Let p ∈ (0, 1/2] and λ = √(log₂(1/p)) ≥ 1. Let K ⊆ [−1,1]^m be a convex
body so that 0 ∈ K and for every S ⊆ [m], Vol_S(K_S) ≥ p 2^{|S|}. Then for every a ∈ ℝ^m,
K_a := K ∩ {x ∈ [−1,1]^m : ⟨a, x⟩ ≤ λ/√m · ‖a‖₁} has volume Vol_m(K_a) ≥ p 2^{−2m}."

`m ≥ 1`, the dimension at which `λ/√m` is defined. Every coordinate section (including `S = ∅`)
is measured by `|S|`-dimensional Lebesgue measure. -/
theorem lemma_24 {m : ℕ} (hm : 0 < m) (p : ℝ) (hp0 : 0 < p) (hp : p ≤ 1 / 2)
    (K : Set (Fin m → ℝ)) (hK : IsConvexBody K) (hKcube : K ⊆ cube m) (h0 : (0 : Fin m → ℝ) ∈ K)
    (hsec : ∀ S : Finset (Fin m), p * 2 ^ S.card ≤ (volume (coordSection K S)).toReal)
    (a : Fin m → ℝ) :
    p * ((2 : ℝ) ^ (2 * m))⁻¹ ≤
      (volume (K ∩ {x ∈ cube m |
        ∑ i, a i * x i ≤ Real.sqrt (Real.logb 2 (1 / p)) / Real.sqrt m * ∑ i, |a i|})).toReal := by sorry

end L1Sparsifiers.Main
