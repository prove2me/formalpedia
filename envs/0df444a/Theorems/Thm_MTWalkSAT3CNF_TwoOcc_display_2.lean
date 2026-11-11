-- Prove2me | Theorems.Thm_MTWalkSAT3CNF_TwoOcc_display_2
-- name    : MTWalkSAT3CNF.TwoOcc.display_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T21:26:59.231762+00:00
-- url     : https://prove2.me/theorems/c047b69e-3d4c-4f55-8f41-a75602307962
-- title:
--   §3.2 display (2) — the potential satisfies $0\le\Phi\le m$
-- statement:
--   Assume $\Delta(F)\le2$ and that every variable occurring twice has one positive and one negative occurrence. For every assignment $\sigma$ the global potential of display (1) satisfies
--
--   $$0\le\Phi(\sigma)\le m .$$
--
--   The upper bound converts the drift of $\Phi$ into the WalkSAT bound $\mathbb E[T_{WS}]\le4m$ (display (5)).
--
--   Differences from the source:
--   - encoding: Φ as a sum over defect trees and boundary trees → Φ as a sum over clauses that are roots of a defect tree or a boundary tree of their component, every other component contributing 0; reason: by Lemma 3.5 each defect tree and each boundary tree has exactly one such root; the sums are equal
-- source:
--   Minbo Gao, Kun He, Tao Jiang, Tight Variable-Occurrence Bounds and Exponential Separations for Moser–Tardos and WalkSAT on 3-CNF, STOC 2027 submission #914 (October 2026), §3.2, display (2), p. 14. https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/914.pdf

import Definitions.Def_MTWalkSAT3CNF_TwoOcc_Potential

set_option autoImplicit false

namespace MTWalkSAT3CNF.TwoOcc

/-- §3.2 display (2), p. 14: in the opposite-sign case with `Δ(F) ≤ 2`, the global potential
satisfies `0 ≤ Φ ≤ m` for every assignment. -/
theorem display_2 {V : Type*} [Fintype V] [DecidableEq V] {m : ℕ} (F : Formula V m)
    (hΔ : MaxOccLeTwo F) (hopp : OppositeSign F) (σ : V → Bool) :
    0 ≤ potential F σ ∧ potential F σ ≤ m := by sorry

end MTWalkSAT3CNF.TwoOcc
