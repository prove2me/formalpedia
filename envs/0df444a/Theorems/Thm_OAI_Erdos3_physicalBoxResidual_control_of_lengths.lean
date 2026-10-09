-- Prove2me | Theorems.Thm_OAI_Erdos3_physicalBoxResidual_control_of_lengths
-- name    : OAI.Erdos3.physicalBoxResidual_control_of_lengths
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-10-08T17:49:08.15427+00:00
-- url     : https://prove2.me/theorems/8c228125-8e30-4fc1-889e-edd5992a96fb
-- title:
--   Long enough cells give residue truncation control on every cell of a physical box
-- statement:
--   Let $I$ and $\iota$ be finite types with decidable equality. Let $\mathrm{lo} : I \to \mathbb{Z}$ and $N : I \to \mathbb{N}$, and for each $i$ let $P_i$ be a `FiniteProgressionPartition (N i)` (OpenAI's structure: a finite label type with, for each label, a start, a positive step and a length, identifying the disjoint union of the progressions with $\{0, \dots, N_i - 1\}$) all of whose cells have step $1$ and positive length. Let $q : \iota \to \mathbb{N}$ take nonzero, pairwise coprime values, let $b \in \mathbb{N}$, and let $f : (I \to \mathbb{Z}) \to \mathbb{R}$ satisfy $0 \le f(x) \le 1$ on the box `translatedIntegerBox lo N` $= \{\mathrm{lo} + y : 0 \le y_i < N_i\}$. Let $\mathrm{modLog}, \mathrm{dimLog}, \mathrm{accLog}, \eta$ be real numbers with $0 \le \mathrm{modLog}$, $\eta \le 1$, $e^{-\mathrm{accLog}} \le \eta$, $q_j \le e^{\mathrm{modLog}}$ for every $j \in \iota$, and $|I| \le e^{\mathrm{dimLog}}$, and suppose every cell of every $P_i$ has length at least $\exp(\mathrm{modLog} \cdot 2b + \mathrm{accLog} + \mathrm{dimLog} + 1)$. Then for every label tuple $c = (c_i)_i$, the predicate `ResiduePhysicalTruncationControl` holds for $q$, $b$, $f$, $\eta$ on the cell of $c$: the subbox with lower corner $\mathrm{lo}_i + \mathrm{start}(c_i)$ (`intervalCellLower`) and side lengths $\mathrm{length}(c_i)$, taken with modulus $1$ and residue $0$ (its nonemptiness supplied by the lemma `physicalBoxCell_nonempty`). This predicate of OpenAI's bounds, with tolerance $\eta$ and the factor `residueTruncationCap ι b η`, the mean squares of $f$'s degree-$\le b$ prime-coordinate truncation `residuePhysicalTruncation` and of $f$ minus it on the cell, and the correlation of that difference with any test function of the prime-coordinate residues depending on at most $b$ of the moduli.
--
--   Lean: `OAI.Erdos3.physicalBoxResidual_control_of_lengths` in `lean/OAI/Combinatorics/Progressions/Geometry/PhysicalBoxControl.lean` (OpenAI); the definitions it uses are in the definitions bundles `OAIErdos3B090` of this split (and the bundles they import).
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/Progressions/Geometry/PhysicalBoxControl.lean#L124

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIErdos3B090

namespace OAI

section

namespace Erdos3

open scoped BigOperators Classical

variable {I ι : Type*} [Fintype I] [DecidableEq I] [Fintype ι] [DecidableEq ι]

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical

theorem physicalBoxResidual_control_of_lengths {I ι : Type*}
    [Fintype I] [DecidableEq I] [Fintype ι] [DecidableEq ι]
    (lo : I → ℤ) (N : I → ℕ) (P : ∀ i, FiniteProgressionPartition (N i))
    (hstep : ∀ i c, (P i).step c = 1) (hpos : ∀ i c, 0 < (P i).length c)
    (q : ι → ℕ) [∀ j, NeZero (q j)] (hpair : Pairwise (fun i j => (q i).Coprime (q j)))
    (b : ℕ) (f : (I → ℤ) → ℝ) (hf : ∀ x ∈ translatedIntegerBox lo N, 0 ≤ f x ∧ f x ≤ 1)
    (modLog dimLog accLog eta : ℝ) (hmodLog : 0 ≤ modLog) (heta : eta ≤ 1)
    (hacc : Real.exp (-accLog) ≤ eta) (hmoduli : ∀ j, (q j : ℝ) ≤ Real.exp modLog)
    (hdim : (Fintype.card I : ℝ) ≤ Real.exp dimLog)
    (hlength : ∀ i c, Real.exp (modLog * (2 * b : ℕ) + accLog + dimLog + 1) ≤ ((P i).length c : ℝ))
    (c : ∀ i, (P i).Label) :
    ResiduePhysicalTruncationControl (fun i => intervalCellLower (lo i) (P i) (c i))
      (fun i => (P i).length (c i)) 1 (fun _ => 0) (physicalBoxCell_nonempty lo N P hpos c) q b f eta := by
  sorry

end Erdos3
end
end OAI
