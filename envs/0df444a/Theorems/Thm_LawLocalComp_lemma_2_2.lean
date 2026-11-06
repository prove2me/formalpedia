-- Prove2me | Theorems.Thm_LawLocalComp_lemma_2_2
-- name    : LawLocalComp.lemma_2_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T03:12:41.012104+00:00
-- url     : https://prove2.me/theorems/8b0aef91-9b64-49f3-be34-c3386ec571a9
-- title:
--   Lemma 2.2 (Capped-tail envelope)
-- statement:
--   Let $Y$ be a finite nonnegative law, $M_Y(k)=\mathbb E\max\{Y_1,\dots,Y_k\}$ for iid copies, and
--   $$H_Y(k)=\int_0^\infty\min\{1,k\,\mathbb P(Y\ge t)\}\,dt\qquad(k\ge0).$$
--   1. For every integer $k\ge1$, $\tfrac12H_Y(k)\le M_Y(k)\le H_Y(k)$.
--   2. If $Y$ has $s$ positive atoms, $H_Y$ is nonnegative, nondecreasing and concave on $[0,\infty)$, with at most $s$ breakpoints: there is a set $B$ of at most $s$ reals such that $H_Y$ is affine on every interval of $[0,\infty)$ whose interior avoids $B$.
--
--   The envelope turns expected maxima, which the maximum-norm contract controls, into piecewise affine functions whose number of pieces counts atoms.
--
--   Differences from the source:
--   - reading: increasing → monotone (nondecreasing) on [0, ∞); reason: H_Y ≡ 0 when Y is the point mass at 0, so strict increase is false there
--   - reading: at most s breakpoints → a set B of at most s reals such that H_Y is affine on every [u, v] ⊆ [0, ∞) whose interior avoids B; reason: the definition of a breakpoint of a piecewise affine function
-- source:
--   Mahboub–Rahgoshay, Optimal Law-Local Compression for Stochastic Loads, STOC 2027 submission (manuscript of Oct. 29, 2026, sha256 5f71501c…aa873), Lemma 2.2, p.4

import Mathlib
import Definitions.Def_LawLocalComp_expMax
import Definitions.Def_LawLocalComp_capTail

namespace LawLocalComp

/-- **Lemma 2.2 (Capped-tail envelope).**
Mahboub–Rahgoshay, *Optimal Law-Local Compression for Stochastic Loads*, STOC 2027
submission manuscript of Oct. 29, 2026 (sha256 5f71501c…aa873), Lemma 2.2, p.4.

For a finite nonnegative law `Y`, `M_Y(k)` the expected maximum of `k` iid copies and
`H_Y(k) = ∫_0^∞ min{1, kP(Y ≥ t)} dt`: for integers `k ≥ 1`, `H_Y(k)/2 ≤ M_Y(k) ≤ H_Y(k)`; and if `Y`
has `s` positive atoms, `H_Y` is nonnegative, increasing and concave on `k ≥ 0`, with at most `s`
breakpoints.

**Formalization Note.** "Increasing" is monotone (`H_Y ≡ 0` when `Y = 0`). "At most `s` breakpoints":
a set `B` of at most `s` reals such that `H_Y` is affine on every interval of `[0, ∞)` whose interior
avoids `B`. -/
theorem lemma_2_2 (Y : Law) :
    (∀ k : ℕ, 1 ≤ k → capTail Y k / 2 ≤ expMax Y k ∧ expMax Y k ≤ capTail Y k) ∧
    (∀ k : ℝ, 0 ≤ k → 0 ≤ capTail Y k) ∧ MonotoneOn (capTail Y) (Set.Ici 0) ∧
    ConcaveOn ℝ (Set.Ici 0) (capTail Y) ∧
    ∃ B : Finset ℝ, B.card ≤ (Y.w.support.filter (fun y => 0 < y)).card ∧
      ∀ u v : ℝ, 0 ≤ u → u < v → (∀ β ∈ B, β ≤ u ∨ v ≤ β) →
        ∃ α₀ α₁ : ℝ, ∀ k ∈ Set.Icc u v, capTail Y k = α₀ + α₁ * k := by sorry

end LawLocalComp
