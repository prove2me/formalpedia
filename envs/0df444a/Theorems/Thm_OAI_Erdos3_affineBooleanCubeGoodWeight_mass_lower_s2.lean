-- Prove2me | Theorems.Thm_OAI_Erdos3_affineBooleanCubeGoodWeight_mass_lower_s2
-- name    : OAI.Erdos3.affineBooleanCubeGoodWeight_mass_lower_s2
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-17T10:41:04.18546+00:00
-- url     : https://prove2.me/theorems/93f4bbda-6975-4740-b115-761aad7af998
-- title:
--   Lower bound for the total mass of the affine Boolean cube good weight
-- statement:
--   Let $B, O, J, \alpha$ be finite types, with $B$, $O$, $\alpha$ having decidable equality, and let $h$ be a natural number. Write `BlockParameter B (Fin h) α` $= B \times \operatorname{Fin} h \times \mathrm{Option}\ \alpha$ and consider real functions $a$ on it. Let $c : J \to B \to \mathbb{R}$, `sets` $: O \to$ finite subsets of $\alpha$, `block` $: J \to O \to B$, $v \in \operatorname{Fin} h$, `sel` $: J \to O \to \mathrm{Option}\ \alpha$, $L$ a continuous linear map from (`BlockParameter B (Fin h) α` $\to \mathbb{R}$) to itself, $b$ a real function on `BlockParameter B (Fin h) α`, $\psi : \mathbb{R} \to \mathbb{R}$, $r : B \times \operatorname{Fin} h \to \mathbb{R}$ and $\kappa : J \to \mathbb{R}$.
--
--   Assume $\psi$ is infinitely differentiable, $\psi(t) \in [0, 1]$ for all $t$, $\psi(t) = 1$ whenever $|t| \ge 2$, $r_i > 0$ for all $i$, and $\kappa_j > 0$ for all $j$. Then
--   $$1 - c_\alpha \sum_i r_i - \sum_{j \in J} \mu\bigl(\{a : |\texttt{booleanMinorDeterminant}(c_j, \texttt{sets}, \texttt{block}_j, v, \texttt{sel}_j, b + L a)| < 2\kappa_j\}\bigr) \le \int \texttt{affineBooleanCubeGoodWeight c sets block v sel L b psi r kappa}(a)\, da.$$
--   Here $c_\alpha$ = `scalarCubeBoundaryConstant α` (an explicit positive constant of OpenAI); $\mu$ = `blockCubeMeasure B (Fin h) α`, OpenAI's probability measure on real functions on `BlockParameter B (Fin h) α` (the image of a product of scalar cube measures), and $\mu(\cdot)$ is its real value; `booleanMinorDeterminant c sets block v r a` is OpenAI's determinant of the selected Boolean minor (a square matrix of polynomials indexed by $O$) evaluated at $a$; the integral on the right is with respect to Lebesgue measure on real functions on `BlockParameter B (Fin h) α`; and `affineBooleanCubeGoodWeight` is OpenAI's weight: the scalar cube product weight with radii $r$ multiplied by the product over $j$ of sublevel cutoffs built from $\psi$, $\kappa_j$ and the determinant $a \mapsto$ `booleanMinorDeterminant` at $b + L a$, transported to `BlockParameter` coordinates.
--
--   Lean: `OAI.Erdos3.affineBooleanCubeGoodWeight_mass_lower_s2`, which states OpenAI's `OAI.Erdos3.affineBooleanCubeGoodWeight_mass_lower` (in `lean/OAI/Combinatorics/Progressions/Lattices/AffineCubeMinorGoodMass.lean`); the definitions it uses are in the definitions bundle `OAIE3v2B100` of version 2 of this split (and the bundles they import).
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/Progressions/Lattices/AffineCubeMinorGoodMass.lean (declaration OAI.Erdos3.affineBooleanCubeGoodWeight_mass_lower)

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIE3v2B100

section

namespace OAI

section

namespace Erdos3

open MeasureTheory
open scoped ContDiff BigOperators

variable {B O J α : Type*} [Fintype B] [Fintype O] [Fintype J] [Fintype α]
  [DecidableEq B] [DecidableEq O] [DecidableEq α] {h : ℕ}

variable (c : J → B → ℝ) (sets : O → Finset α) (block : J → O → B)
  (v : Fin h) (sel : J → O → Option α)
  (L : (BlockParameter B (Fin h) α → ℝ) →L[ℝ] (BlockParameter B (Fin h) α → ℝ))
  (b : BlockParameter B (Fin h) α → ℝ)
  (ψ : ℝ → ℝ) (r : B × Fin h → ℝ) (κ : J → ℝ)

theorem affineBooleanCubeGoodWeight_mass_lower_s2
    (hψ : ContDiff ℝ ∞ ψ) (hrange : ∀ t, ψ t ∈ Set.Icc (0 : ℝ) 1)
    (hone : ∀ t, 2 ≤ |t| → ψ t = 1) (hr : ∀ i, 0 < r i) (hκ : ∀ j, 0 < κ j) :
    1 - scalarCubeBoundaryConstant α * ∑ i, r i -
        ∑ j, (blockCubeMeasure B (Fin h) α).real
          {a | |booleanMinorDeterminant (c j) sets (block j) v (sel j) (b + L a)| < 2 * κ j} ≤
      ∫ a, affineBooleanCubeGoodWeight c sets block v sel L b ψ r κ a := by
  sorry

end Erdos3

end

end OAI
end
