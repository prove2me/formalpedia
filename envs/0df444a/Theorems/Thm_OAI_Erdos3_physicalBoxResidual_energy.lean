-- Prove2me | Theorems.Thm_OAI_Erdos3_physicalBoxResidual_energy
-- name    : OAI.Erdos3.physicalBoxResidual_energy
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-08T17:23:23.574371+00:00
-- url     : https://prove2.me/theorems/a4d2cff9-9b62-4e33-a99c-a7c3298f7b1e
-- title:
--   Cellwise truncation control bounds the mean square of the physical box residual
-- statement:
--   Let $I$ and $\iota$ be finite types with decidable equality. Let $\mathrm{lo} : I \to \mathbb{Z}$ and $N : I \to \mathbb{N}$ be such that the box `translatedIntegerBox lo N` $= \{\mathrm{lo} + y : 0 \le y_i < N_i\}$ is nonempty, and for each $i$ let $P_i$ be a `FiniteProgressionPartition (N i)` (OpenAI's structure: a finite label type with, for each label, a start, a positive step and a length, identifying the disjoint union of the progressions with $\{0, \dots, N_i - 1\}$) all of whose cells have step $1$ and positive length, so that the label tuples $c = (c_i)_i$ index a partition of the box into subboxes. Let $q : \iota \to \mathbb{N}$ take nonzero values, $b \in \mathbb{N}$, $f : (I \to \mathbb{Z}) \to \mathbb{R}$ and $\eta \in \mathbb{R}$. Suppose that for every label tuple $c$ the predicate `ResiduePhysicalTruncationControl` holds for $q$, $b$, $f$, $\eta$ on the cell of $c$ (the subbox with lower corner $\mathrm{lo}_i + \mathrm{start}(c_i)$ and side lengths $\mathrm{length}(c_i)$, taken with modulus $1$ and residue $0$). This predicate of OpenAI's bounds, with tolerance $\eta$ and the factor `residueTruncationCap ι b η`, the mean squares of $f$'s degree-$\le b$ prime-coordinate truncation `residuePhysicalTruncation` and of $f$ minus it on the cell, and the correlation of that difference with any test function of the prime-coordinate residues depending on at most $b$ of the moduli. Then, for $x$ uniform on the box,
--   $$\mathbb{E}_x\bigl[r(x)^2\bigr] \le 1 + \eta\, \kappa^2,$$
--   where $r = $ `physicalBoxResidual lo N P hpos q b f` (on the box, $f$ minus its cellwise truncation `physicalBoxTruncation`) and $\kappa = $ `residueTruncationCap ι b η` $= |\{S \subseteq \iota : |S| \le b\}| \cdot 2^b (1 + \eta)$.
--
--   Lean: `OAI.Erdos3.physicalBoxResidual_energy` in `lean/OAI/Combinatorics/Progressions/Geometry/PhysicalBoxControl.lean` (OpenAI); the definitions it uses are in the definitions bundles `OAIErdos3B090` of this split (and the bundles they import).
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/Progressions/Geometry/PhysicalBoxControl.lean#L70

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIErdos3B090

namespace OAI

section

namespace Erdos3

open scoped BigOperators Classical

variable {I ι : Type*} [Fintype I] [DecidableEq I] [Fintype ι] [DecidableEq ι]

theorem physicalBoxResidual_energy (lo : I → ℤ) (N : I → ℕ)
    [Nonempty (translatedIntegerBox lo N)]
    (P : ∀ i, FiniteProgressionPartition (N i)) (hstep : ∀ i c, (P i).step c = 1)
    (hpos : ∀ i c, 0 < (P i).length c) (q : ι → ℕ) [∀ j, NeZero (q j)]
    (b : ℕ) (f : (I → ℤ) → ℝ) (eta : ℝ)
    (hc : ∀ c : (∀ i, (P i).Label), ResiduePhysicalTruncationControl (fun i => intervalCellLower (lo i) (P i) (c i))
      (fun i => (P i).length (c i)) 1 (fun _ => 0) (physicalBoxCell_nonempty lo N P hpos c) q b f eta) :
    (FiniteProbabilityWeights.uniform (translatedIntegerBox lo N)).mean
      (fun x => physicalBoxResidual lo N P hpos q b f x.val ^ 2) ≤
      1 + eta * residueTruncationCap ι b eta ^ 2 := by
  sorry

end Erdos3
end
end OAI
