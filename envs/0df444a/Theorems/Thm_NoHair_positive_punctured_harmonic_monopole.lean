-- Prove2me | Theorems.Thm_NoHair_positive_punctured_harmonic_monopole
-- name    : NoHair.positive_punctured_harmonic_monopole
-- status  : Open
-- author  : @Igor Valuev
-- created : 2026-11-23T06:57:55.186524+00:00
-- url     : https://prove2.me/theorems/32a64010-9132-4bbf-a957-70eddf17bf2c
-- title:
--   Nonnegative harmonic factors on punctured three-space normalized at infinity
-- statement:
--   A nonnegative harmonic function on $\mathbb R^3\setminus\{0\}$ with limit $1$ at infinity has the form $U(x)=1+b/|x|$ for some $b\ge0$. No asymptotic coefficient or rate is prescribed at the puncture. This global consequence of Bôcher’s theorem is the potential-theoretic rigidity used after a static vacuum conformal double has been identified with Euclidean space.
-- source:
--   S. Axler, P. Bourdon and W. Ramey, Harmonic Function Theory, second edition, Chapter 3, Bôcher’s theorem, https://www.axler.net/HFT.pdf. Apply Bôcher locally, remove the Newton pole, and use the limit at infinity.

import Mathlib.Analysis.InnerProductSpace.Harmonic.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2

open Set InnerProductSpace

theorem NoHair.positive_punctured_harmonic_monopole (U : EuclideanSpace ℝ (Fin 3) → ℝ)
    (hh : HarmonicOnNhd U ({0}ᶜ)) (hpos : ∀ x, x ≠ 0 → 0 ≤ U x)
    (hfar : ∀ ε : ℝ, 0 < ε → ∃ L : ℝ, ∀ x, L < ‖x‖ → |U x - 1| ≤ ε) :
    ∃ b : ℝ, 0 ≤ b ∧ ∀ x, x ≠ 0 → U x = 1 + b / ‖x‖ := by sorry
