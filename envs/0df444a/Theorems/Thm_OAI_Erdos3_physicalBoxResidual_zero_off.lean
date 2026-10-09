-- Prove2me | Theorems.Thm_OAI_Erdos3_physicalBoxResidual_zero_off
-- name    : OAI.Erdos3.physicalBoxResidual_zero_off
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-08T17:23:06.364235+00:00
-- url     : https://prove2.me/theorems/fe037170-5c8d-4e46-a8c0-f3ef556512f3
-- title:
--   The physical box residual vanishes off the box
-- statement:
--   Let $I$ and $\iota$ be finite types with decidable equality. Let $\mathrm{lo} : I \to \mathbb{Z}$ and $N : I \to \mathbb{N}$, and for each $i$ let $P_i$ be a `FiniteProgressionPartition (N i)` (OpenAI's structure bundling a finite label type and, for each label, a start, a positive step and a length, together with an identification of the disjoint union of the progressions $\{\mathrm{start} + \mathrm{step}\cdot j : j < \mathrm{length}\}$ with $\{0, \dots, N_i - 1\}$), all of whose cells have positive length (`hpos`). Let $q : \iota \to \mathbb{N}$ take nonzero values, $b \in \mathbb{N}$, $f : (I \to \mathbb{Z}) \to \mathbb{R}$, and let $x : I \to \mathbb{Z}$ lie outside `translatedIntegerBox lo N`, the box $\{\mathrm{lo} + y : 0 \le y_i < N_i \text{ for all } i\}$. Then `physicalBoxResidual lo N P hpos q b f x` $= 0$. (`physicalBoxResidual` is OpenAI's function equal, on the box, to $f$ minus its cellwise low-degree prime-coordinate truncation `physicalBoxTruncation`, and to $0$ off the box.)
--
--   Lean: `OAI.Erdos3.physicalBoxResidual_zero_off` in `lean/OAI/Combinatorics/Progressions/Geometry/PhysicalBoxControl.lean` (OpenAI); the definitions it uses are in the definitions bundles `OAIErdos3B090` of this split (and the bundles they import).
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/Progressions/Geometry/PhysicalBoxControl.lean#L27

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIErdos3B090

namespace OAI

section

namespace Erdos3

open scoped BigOperators Classical

variable {I ι : Type*} [Fintype I] [DecidableEq I] [Fintype ι] [DecidableEq ι]

theorem physicalBoxResidual_zero_off (lo : I → ℤ) (N : I → ℕ)
    (P : ∀ i, FiniteProgressionPartition (N i)) (hpos : ∀ i c, 0 < (P i).length c)
    (q : ι → ℕ) [∀ j, NeZero (q j)] (b : ℕ) (f : (I → ℤ) → ℝ)
    (x : I → ℤ) (hx : x ∉ translatedIntegerBox lo N) :
    physicalBoxResidual lo N P hpos q b f x = 0 := by
  sorry

end Erdos3
end
end OAI
