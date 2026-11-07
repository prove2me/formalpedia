-- Prove2me | Theorems.Thm_OnlineCAP_theorem_4_1_rotation
-- name    : OnlineCAP.theorem_4_1_rotation
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T07:26:24.152178+00:00
-- url     : https://prove2.me/theorems/3d6f3f6b-4450-4fc9-a8fd-5cae8bef1789
-- title:
--   Proof of Theorem 4.1 — by rotation, O(log log n)-rounding for topless and for leftless rectangles
-- statement:
--   There is a function $\alpha(n)=O(\log\log n)$ such that for every finite point set $P\subseteq\mathbb R^2$ with $n=|P|$:
--
--   1. the traces of topless rectangles on $P$ have an $\alpha(n)$-rounding algorithm;
--   2. the traces of leftless rectangles on $P$ have an $\alpha(n)$-rounding algorithm.
--
--   This is the first step of the proof of Theorem 4.1: Theorem 4.3, applied after rotating the coordinate axes.
--
--   Differences from the source:
--   - encoding: an O(log log n)-rounding algorithm for each family → one function α =O[atTop] log log n serving both families; reason: the maximum of two O(log log n) functions is O(log log n)
-- source:
--   Hathcock, Subramanian, Umboh, Zlatin, Weighted and Unweighted Online Connectivity Augmentation via Geometric Hitting Set (manuscript of Nov. 3, 2026, sha256 e3b9cb64…), proof of Theorem 4.1, p.21

import Mathlib
import Definitions.Def_OnlineCAP_RandOnlineAlg
import Definitions.Def_OnlineCAP_IsRounding
import Definitions.Def_OnlineCAP_traceFam
import Definitions.Def_OnlineCAP_IsTopless
import Definitions.Def_OnlineCAP_IsLeftless

open MeasureTheory Filter Asymptotics

namespace OnlineCAP

/-- **Rotation step of the proof of Theorem 4.1.** Hathcock–Subramanian–Umboh–Zlatin, *Weighted and Unweighted Online Connectivity
Augmentation via Geometric Hitting Set*, manuscript of Nov. 3, 2026 (sha256 e3b9cb64…), proof of Theorem 4.1, p.21 (PDF p.21):
"By rotation of the coordinate axes, Theorem 4.3 holds identically for topless and leftless
rectangles, yielding an O(log log n)-rounding algorithm for each family."

There is a function `α(n) = O(log log n)` such that for every finite point set `P ⊆ ℝ²` with
`n = |P|` there is an `α(n)`-rounding algorithm for the traces on `P` of topless rectangles, and
one for the traces of leftless rectangles.

**Formalization Note.** One function `α` serves both families (take the larger of two). -/
theorem theorem_4_1_rotation : ∃ α : ℕ → ℝ, α =O[atTop] (fun n : ℕ => Real.log (Real.log n)) ∧
    ∀ P : Finset (ℝ × ℝ),
      (∃ A : RandOnlineAlg ↥P (Set ↥P × (↥P → ℝ)),
        IsRounding (traceFam P IsTopless) A (α P.card)) ∧
      (∃ A : RandOnlineAlg ↥P (Set ↥P × (↥P → ℝ)),
        IsRounding (traceFam P IsLeftless) A (α P.card)) := by sorry

end OnlineCAP
