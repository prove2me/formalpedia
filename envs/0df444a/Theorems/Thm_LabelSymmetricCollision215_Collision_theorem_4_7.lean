-- Prove2me | Theorems.Thm_LabelSymmetricCollision215_Collision_theorem_4_7
-- name    : LabelSymmetricCollision215.Collision.theorem_4_7
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T07:58:57.346824+00:00
-- url     : https://prove2.me/theorems/a319f06d-1a55-4a5d-bd3e-57e344aee99b
-- title:
--   Theorem 4.7 — Minimal Specht dimension
-- statement:
--   Assume $s\ge1$ and $N\ge2s$. For every partition $\mu$ of $s$,
--   $$\dim S^{(N-s,\mu)}\ge\binom Ns-\binom N{s-1}.$$
--   Equivalently, the same lower bound holds for the minimum over all partitions of $s$. This is the cited Specht-dimension estimate.
--
--   Differences from the source:
--   - encoding: complex Specht modules and standard-tableau multiplicities → published Young left ideals and increasing bijective fillings, transported to cyclic range labels; reason: these are concrete realizations of the same representations and multiplicity sets; height caps exclude no partition of the specified size
--   - encoding: minimum dimension over partitions μ of s → the bound for every such μ, with subtraction in the real numbers; reason: the finite nonempty partition family makes the formulations equivalent; no default infimum or truncated dimension bound occurs
-- source:
--   Frédéric Magniez, Sebastian Zur, Tight Time-Space Lower Bounds for Collision Finding and Element Distinctness under Label Symmetry, STOC 2027 submission #215 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/215.pdf, Theorem 4.7, PDF 24 / printed 22

import Definitions.Def_LabelSymmetricCollision215_Collision_Specht

namespace LabelSymmetricCollision215.Collision

/-- Magniez–Zur, Theorem 4.7, PDF 24 / printed 22. -/
theorem theorem_4_7 (N s : ℕ) (hs : 1 ≤ s) (hN : 2*s ≤ N) :
    ∀ μ : Shape s, (Nat.choose N s : ℝ) - Nat.choose N (s-1) ≤
      Module.finrank ℂ (Specht (liftedShape hN μ)) := by sorry

end LabelSymmetricCollision215.Collision
