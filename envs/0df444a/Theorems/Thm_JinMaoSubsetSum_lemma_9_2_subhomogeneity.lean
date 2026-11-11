-- Prove2me | Theorems.Thm_JinMaoSubsetSum_lemma_9_2_subhomogeneity
-- name    : JinMaoSubsetSum.lemma_9_2_subhomogeneity
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T10:39:08.975795+00:00
-- url     : https://prove2.me/theorems/6fdd22ff-27e0-45a2-a1c8-2d71e5f04981
-- title:
--   Lemma 9.2 — $\mathrm{vol}_d(\pi_\Lambda(aK))/a^d\ge\mathrm{vol}_d(\pi_\Lambda(bK))/b^d$ for $0<a\le b$
-- statement:
--   **Lemma 9.2.** Let $\Lambda\subseteq\mathbb R^d$ be a lattice and $K\subseteq\mathbb R^d$ a convex body. For $0<a\le b$,
--   $$
--   \frac{\mathrm{vol}_d(\pi_\Lambda(aK))}{a^d}\ \ge\ \frac{\mathrm{vol}_d(\pi_\Lambda(bK))}{b^d}.
--   $$
--
--   Volume measured in the quotient $\mathbb R^d/\Lambda$ grows at most like the $d$-th power under dilation of a convex body. It is used to bound the volume of quotient shells (Lemma 9.3) and of caps.
--
--   **Formalization Note** $\mathrm{vol}_d(\pi_\Lambda(\cdot))$ is `qvol Λ` with values in $[0,\infty]$; the inequality is multiplied out, $a^d\,\mathrm{vol}_d(\pi_\Lambda(bK))\le b^d\,\mathrm{vol}_d(\pi_\Lambda(aK))$, equivalent since $0<a^d,b^d<\infty$.
--
--   Differences from the source:
--   - encoding: vol_d(π_Λ(·)) and the quotient inequality → qvol Λ in [0, ∞]; a^d · qvol(bK) ≤ b^d · qvol(aK); reason: the same inequality, multiplied by the positive finite a^d b^d; Λ any discrete subgroup
-- source:
--   Jin, Mao, Subset Sum in Almost-Linear Time, arXiv:2610.20742v1 (sha256 8b604948862d9188e922b8abf95831fde3a3699e26d39177d20a1460e31a926a), Lemma 9.2, p.49 (PDF p.51)

import Mathlib
import Definitions.Def_JinMaoSubsetSum_zonotope
import Definitions.Def_JinMaoSubsetSum_qvol

set_option autoImplicit false

open scoped Pointwise

namespace JinMaoSubsetSum

/-- **Lemma 9.2** (Jin, Mao, *Subset Sum in Almost-Linear Time*, arXiv:2610.20742v1, p.49): "Let
Λ ⊆ ℝ^d be a lattice and K ⊆ ℝ^d be a convex body. For 0 < a ≤ b,
vol_d(π_Λ(aK))/a^d ≥ vol_d(π_Λ(bK))/b^d."

**Formalization Note.** `Λ` is a discrete additive subgroup of any rank; a convex body is compact,
convex, with nonempty interior; `vol_d(π_Λ(·))` is `qvol Λ` (an extended nonnegative real). The
inequality is stated multiplied out, `a^d · vol_d(π_Λ(bK)) ≤ b^d · vol_d(π_Λ(aK))`, which is the
printed one since `0 < a^d, b^d < ∞`. -/
theorem lemma_9_2_subhomogeneity {d : ℕ} (Λ : AddSubgroup (Fin d → ℝ)) [DiscreteTopology Λ]
    (K : Set (Fin d → ℝ)) (hK : IsConvexBody K) (a b : ℝ) (ha : 0 < a) (hab : a ≤ b) :
    ENNReal.ofReal (a ^ d) * qvol Λ (b • K) ≤ ENNReal.ofReal (b ^ d) * qvol Λ (a • K) := by sorry

end JinMaoSubsetSum
