-- Prove2me | Theorems.Thm_OAI_Erdos3_physicalBoxResidual_cell_residue
-- name    : OAI.Erdos3.physicalBoxResidual_cell_residue
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-10-08T18:10:24.461672+00:00
-- url     : https://prove2.me/theorems/5b6406e3-f9dc-461b-9e7a-df6f6203cf52
-- title:
--   On a controlled cell the physical box residual has small mean on each residue class
-- statement:
--   Let $I$ and $\iota$ be finite types with decidable equality. Let $\mathrm{lo} : I \to \mathbb{Z}$ and $N : I \to \mathbb{N}$ be such that the box `translatedIntegerBox lo N` $= \{\mathrm{lo} + y : 0 \le y_i < N_i\}$ is nonempty, and for each $i$ let $P_i$ be a `FiniteProgressionPartition (N i)` (OpenAI's structure: a finite label type with, for each label, a start, a positive step and a length, identifying the disjoint union of the progressions with $\{0, \dots, N_i - 1\}$) all of whose cells have step $1$ and positive length, so that label tuples $c = (c_i)_i$ index a partition of the box into subboxes and `physicalBoxCell lo N P x` is the label tuple of the cell containing a point $x$ of the box. Let $q : \iota \to \mathbb{N}$ take nonzero, pairwise coprime values, $b \in \mathbb{N}$, $f : (I \to \mathbb{Z}) \to \mathbb{R}$, $\eta \in \mathbb{R}$ and $c$ a label tuple. Suppose `ResiduePhysicalTruncationControl` holds for $q$, $b$, $f$, $\eta$ on the cell of $c$ (the subbox with lower corner $\mathrm{lo}_i + \mathrm{start}(c_i)$ and side lengths $\mathrm{length}(c_i)$, with modulus $1$ and residue $0$); this predicate of OpenAI's bounds, with tolerance $\eta$ and the factor `residueTruncationCap ι b η`, the mean squares of $f$'s degree-$\le b$ prime-coordinate truncation `residuePhysicalTruncation` and of $f$ minus it on the cell, and the correlation of that difference with any test function of the prime-coordinate residues depending on at most $b$ of the moduli. Let $J \subseteq \iota$ be a finite set with $|J| \le b$, let $m$ be a nonzero natural number dividing $\prod_{j \in J} q_j$, and let $\rho : I \to \mathbb{Z}/m$. Write $r = $ `physicalBoxResidual lo N P hpos q b f` (on the box, $f$ minus its cellwise truncation `physicalBoxTruncation`), and $\kappa = $ `residueTruncationCap ι b η` $= |\{S \subseteq \iota : |S| \le b\}| \cdot 2^b (1 + \eta)$. Then, with $x$ uniform on the box,
--   $$\Bigl|\mathbb{E}_x\bigl[\mathbf{1}\{\texttt{physicalBoxCell}(x) = c,\ x \bmod m = \rho\}\, r(x)\bigr]\Bigr| \le \Pr_x\bigl[\texttt{physicalBoxCell}(x) = c\bigr] \cdot \frac{\eta\, \kappa}{m^{|I|}},$$
--   where $x \bmod m$ is the coordinatewise reduction `integerVectorResidue m x`; the left side is OpenAI's `finiteCellResidueMean` and the probability is the weight of $c$ under `finiteCellWeights`.
--
--   Lean: `OAI.Erdos3.physicalBoxResidual_cell_residue` in `lean/OAI/Combinatorics/Progressions/Geometry/PhysicalBoxControl.lean` (OpenAI); the definitions it uses are in the definitions bundles `OAIErdos3B090` of this split (and the bundles they import).
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/Progressions/Geometry/PhysicalBoxControl.lean#L84

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIErdos3B090

namespace OAI

section

namespace Erdos3

open scoped BigOperators Classical

variable {I ι : Type*} [Fintype I] [DecidableEq I] [Fintype ι] [DecidableEq ι]

theorem physicalBoxResidual_cell_residue (lo : I → ℤ) (N : I → ℕ)
    [Nonempty (translatedIntegerBox lo N)]
    (P : ∀ i, FiniteProgressionPartition (N i)) (hstep : ∀ i c, (P i).step c = 1)
    (hpos : ∀ i c, 0 < (P i).length c) (q : ι → ℕ) [∀ j, NeZero (q j)]
    (hpair : Pairwise (fun i j => (q i).Coprime (q j)))
    (b : ℕ) (f : (I → ℤ) → ℝ) (eta : ℝ) (c : ∀ i, (P i).Label)
    (hc : ResiduePhysicalTruncationControl (fun i => intervalCellLower (lo i) (P i) (c i))
      (fun i => (P i).length (c i)) 1 (fun _ => 0) (physicalBoxCell_nonempty lo N P hpos c) q b f eta)
    (J : Finset ι) (hJ : J.card ≤ b) (m : ℕ) [NeZero m] (hm : m ∣ ∏ j ∈ J, q j) (r : I → ZMod m) :
    |finiteCellResidueMean (FiniteProbabilityWeights.uniform (translatedIntegerBox lo N)) (physicalBoxCell lo N P)
      (fun x => integerVectorResidue m x.val) (fun x => physicalBoxResidual lo N P hpos q b f x.val) c r| ≤
      (finiteCellWeights (FiniteProbabilityWeights.uniform (translatedIntegerBox lo N)) (physicalBoxCell lo N P)).weight c *
        (eta * residueTruncationCap ι b eta / (m : ℝ) ^ Fintype.card I) := by
  sorry

end Erdos3
end
end OAI
