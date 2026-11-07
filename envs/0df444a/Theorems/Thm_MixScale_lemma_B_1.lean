-- Prove2me | Theorems.Thm_MixScale_lemma_B_1
-- name    : MixScale.lemma_B_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T21:08:56.51496+00:00
-- url     : https://prove2.me/theorems/7848f608-dafe-4d00-bc2b-978044ff11cd
-- title:
--   Lemma B.1, p.18 — kernel peak and tail
-- statement:
--   For $K(z)=\int_1^2e^{izx}\,dx$ and real $z$, $|K(z)|\le\min(1,2/|z|)$. There is an absolute $c_K>0$ such that for $0<u\le1$,
--
--   $$|z|\ge u\implies|K(z)|\le1-c_Ku^2,$$
--
--   and $|K(z)|\ge1-z^2/24$.
--
--   This separates the correlation peak at a true center from its tail in the pilot scan.
--
--   Differences from the source:
--   - encoding: |K(z)| ≤ min(1, 2/|z|), with 2/0 = ∞ → |K(z)| ≤ 1 for every z, and |K(z)| ≤ 2/|z| for z ≠ 0; reason: Lean's 2/0 = 0 would make the z = 0 case false
--   - generalization: for |z| ≤ u, |K(z)| ≥ 1 − z²/24 → for every real z; reason: the bound holds for all z, so it specializes to |z| ≤ u
-- source:
--   Wang–Zhang, Learning Mixtures with Unknown Scales: Sharp Dependence on Separation, STOC 2027 submission (sha256 5277f95e…), Lemma B.1, p.18 (PDF p.20)

import Mathlib
import Definitions.Def_MixScale_Scalar

namespace MixScale

/-- **Lemma B.1** (Kernel peak and tail).

S. Wang and X. Zhang, *Learning Mixtures with Unknown Scales: Sharp Dependence on Separation*, STOC
2027 submission manuscript (sha256 5277f95e…7c6c), Lemma B.1, p.18 (PDF p.20).

**Formalization Note.** `min(1, 2/|z|)` at `z = 0` is `1` in the paper (`2/0 = ∞`); Lean's `2/0 = 0`,
so the bound `2/|z|` is stated for `z ≠ 0` and the bound `1` for every `z`. The last clause holds for
every real `z` (it needs no `u`), which covers the paper's `|z| ≤ u`. -/
theorem lemma_B_1 :
    (∀ z : ℝ, ‖kernelK z‖ ≤ 1) ∧ (∀ z : ℝ, z ≠ 0 → ‖kernelK z‖ ≤ 2 / |z|) ∧
    (∃ cK : ℝ, 0 < cK ∧ ∀ u z : ℝ, 0 < u → u ≤ 1 → u ≤ |z| → ‖kernelK z‖ ≤ 1 - cK * u ^ 2) ∧
    ∀ z : ℝ, 1 - z ^ 2 / 24 ≤ ‖kernelK z‖ := by sorry

end MixScale
