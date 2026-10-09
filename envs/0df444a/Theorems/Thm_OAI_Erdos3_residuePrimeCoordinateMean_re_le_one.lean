-- Prove2me | Theorems.Thm_OAI_Erdos3_residuePrimeCoordinateMean_re_le_one
-- name    : OAI.Erdos3.residuePrimeCoordinateMean_re_le_one
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-08T17:33:05.862066+00:00
-- url     : https://prove2.me/theorems/0466fbdf-2ca9-46d1-89cd-a00bd3b08e7b
-- title:
--   A cell mean of a function with real part in [0, 1] has real part at most 1
-- statement:
--   Let $\iota$ and $\sigma$ be finite types with decidable equality. Let $g : (\sigma \to \mathbb{Z}) \to \mathbb{C}$, $\mathrm{lo} : \sigma \to \mathbb{Z}$, $N : \sigma \to \mathbb{N}$, $M \in \mathbb{N}$, $a : \sigma \to \mathbb{Z}$, $q : \iota \to \mathbb{N}$, $K$ a finite subset of $\iota$, and $\mathrm{base} \in \prod_{i} (\sigma \to \mathbb{Z}/q_i)$. Suppose $0 \le \operatorname{Re} g(z) \le 1$ for every $z$ in the box `translatedIntegerBox lo N` $= \{\mathrm{lo} + y : 0 \le y_j < N_j\}$. Then $\operatorname{Re}$ `residuePrimeCoordinateMean g lo N M a q K base` $\le 1$. Here `residuePrimeCoordinateMean` is the average of $g(z)$ over the cell `ResiduePrimeCoordinateCell lo N M a q K base`, the set of $z : \sigma \to \mathbb{Z}$ with $\mathrm{lo}_j \le z_j < \mathrm{lo}_j + N_j$ and $z_j \equiv a_j \pmod M$ for all $j$ (OpenAI's `IntegerResidueBox`) and with $z \bmod q_i = \mathrm{base}_i$ coordinatewise for every $i \in K$; the average of the empty family is $0$.
--
--   Lean: `OAI.Erdos3.residuePrimeCoordinateMean_re_le_one` in `lean/OAI/Combinatorics/Progressions/Lattices/ResidueBaselineBounds.lean` (OpenAI); the definitions it uses are in the definitions bundles `OAIErdos3B090` of this split (and the bundles they import).
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/Progressions/Lattices/ResidueBaselineBounds.lean#L9

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIErdos3B090

namespace OAI

section

namespace Erdos3

theorem residuePrimeCoordinateMean_re_le_one {ι σ : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype σ] [DecidableEq σ] (g : (σ → ℤ) → ℂ) (lo : σ → ℤ) (N : σ → ℕ)
    (M : ℕ) (a : σ → ℤ) (q : ι → ℕ) (K : Finset ι) (base : ∀ i, σ → ZMod (q i))
    (hg : ∀ z ∈ translatedIntegerBox lo N, 0 ≤ (g z).re ∧ (g z).re ≤ 1) :
    (residuePrimeCoordinateMean g lo N M a q K base).re ≤ 1 := by
  sorry

end Erdos3
end
end OAI
