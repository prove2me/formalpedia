-- Prove2me | Theorems.Thm_OAI_Erdos3_progressionTuple_residue_riemann_s2
-- name    : OAI.Erdos3.progressionTuple_residue_riemann_s2
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-17T10:31:36.485769+00:00
-- url     : https://prove2.me/theorems/95d0c7ad-3372-4ccb-b1ce-02fffd5b481c
-- title:
--   Riemann-sum comparison for a Lipschitz test along residue-conditioned progression tuples
-- statement:
--   Let $J$ and $I$ be finite types with decidable equality. Let $L, \mathrm{step}, H, M : J \to \mathbb{N}$ and $c : J \to \mathbb{Z}$ with $L_j > 0$, $\mathrm{step}_j > 0$ and $H_j \ge 2$ for all $j$. Let $\delta > 0$, and assume for every $j$ that the progression `integerProgressionSupport (c j) (step j) (H j)` (the integers $c_j + \mathrm{step}_j\, k$ for $0 \le k < H_j$) is contained in $[0, L_j)$ and has at least $\delta L_j$ elements. Let $\mathrm{modulus} : J \to \mathrm{Option}\ I \to \mathbb{N}$ and residues $\mathrm{residue}_{j,i} \in \mathbb{Z}/\mathrm{modulus}_{j,i}$ with $0 < \mathrm{modulus}_{j,i} \le M_j$ for all $j, i$, and assume for every $j$ that $(|I| + 1) M_j \le H_j$ and $c_I \cdot M_j / H_j < \operatorname{vol}(\texttt{scalarCubeDomain } I)$, where $c_I$ = `scalarCubeGridBoundaryConstant I` (an explicit constant of OpenAI) and `scalarCubeDomain I` is OpenAI's set of $a : \mathrm{Option}\ I \to \mathbb{R}$ all of whose scalar cube values lie in $(0, 1)$, with Lebesgue volume. Let $\varepsilon \ge 0$ with $\mathrm{step}_j / L_j \le \varepsilon$ for all $j$. Let $\varphi : (J \to \mathrm{Option}\ I \to \mathbb{R}) \to \mathbb{R}$ be $K$-Lipschitz ($K \in \mathbb{R}_{\ge 0}$), and let $A \ge 0$ with $|\varphi(x)| \le A$ for all $x$.
--
--   Let $P$ be the product over $j$ of the laws `scalarCubeResidueWeights I (H j) (M j) _ (modulus j) (residue j) …` (OpenAI's uniform law on the integer scalar cube box of size $H_j$ conditioned on the residues of the coordinates modulo $\mathrm{modulus}_j$ being $\mathrm{residue}_j$). Then
--   $$\Bigl| \mathbb{E}_{z \sim P}\, \varphi\Bigl((j, i) \mapsto \frac{[i = \mathrm{none}]\, c_j + \mathrm{step}_j\, z_{j,i}}{L_j}\Bigr) - \int \varphi\bigl(\texttt{affineCubeTuple}(\ell, w, x)\bigr)\, d\mu(x) \Bigr| \le \Bigl( \frac{2 A c_I}{\operatorname{vol}(\texttt{scalarCubeDomain } I)} + 2K \Bigr) \sum_j \frac{M_j}{H_j} + K\varepsilon,$$
--   where $[i = \mathrm{none}]$ is $1$ if $i$ is `none` and $0$ otherwise; $\ell_j = c_j / L_j$ and $w_j = \mathrm{step}_j (H_j - 1)/L_j$; `affineCubeTuple ℓ w x` is the tuple $(j, i) \mapsto [i = \mathrm{none}]\,\ell_j + w_j\, x_{j,i}$; and $\mu$ = `scalarCubeProductMeasure J I` is the product over $J$ of OpenAI's normalized Lebesgue probability measure on `scalarCubeDomain I`.
--
--   Lean: `OAI.Erdos3.progressionTuple_residue_riemann_s2`, which states OpenAI's `OAI.Erdos3.progressionTuple_residue_riemann` (in `lean/OAI/Combinatorics/Progressions/Estimates/ProgressionTupleSliceRiemann.lean`); the definitions it uses are in the definitions bundles `OAIE3v2B035`, `OAIE3v2B061`, `OAIE3v2B093` of version 2 of this split (and the bundles they import).
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/Progressions/Estimates/ProgressionTupleSliceRiemann.lean (declaration OAI.Erdos3.progressionTuple_residue_riemann)

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIE3v2B035
import Definitions.Def_OAIE3v2B061
import Definitions.Def_OAIE3v2B093

section

namespace OAI

section

namespace Erdos3

open MeasureTheory
open scoped NNReal BigOperators

variable {J I : Type*} [Fintype J] [Fintype I] [DecidableEq J] [DecidableEq I]

theorem progressionTuple_residue_riemann_s2
    (L step H M : J → ℕ) (c : J → ℤ)
    (hL : ∀ j, 0 < L j) (hstep : ∀ j, 0 < step j) (hH : ∀ j, 2 ≤ H j)
    {δ : ℝ} (hδ : 0 < δ)
    (hsubset : ∀ j, integerProgressionSupport (c j) (step j : ℤ) (H j) ⊆ Finset.Ico (0 : ℤ) (L j : ℤ))
    (hdense : ∀ j, δ * L j ≤ ((integerProgressionSupport (c j) (step j : ℤ) (H j)).card : ℝ))
    (modulus : J → Option I → ℕ) (residue : ∀ j i, ZMod (modulus j i))
    (hm : ∀ j i, 0 < modulus j i) (hmM : ∀ j i, modulus j i ≤ M j)
    (hsize : ∀ j, (Fintype.card I + 1) * M j ≤ H j)
    (hsmall : ∀ j, scalarCubeGridBoundaryConstant I * ((M j : ℝ) / H j) < volume.real (scalarCubeDomain I))
    {ε : ℝ} (hε : 0 ≤ ε) (hmesh : ∀ j, (step j : ℝ) / L j ≤ ε)
    (φ : (J → Option I → ℝ) → ℝ) {K : ℝ≥0} {A : ℝ}
    (hφ : LipschitzWith K φ) (hA : 0 ≤ A) (hb : ∀ x, ‖φ x‖ ≤ A) :
    |(FiniteProbabilityWeights.pi (fun j => scalarCubeResidueWeights I (H j) (M j)
        (by have := hH j; omega) (modulus j) (residue j) (hm j) (hmM j) (hsize j))).mean
        (fun z => φ (fun j i =>
          ((if i = none then (c j : ℝ) else 0) + (step j : ℝ) * (z j i : ℝ)) / L j)) -
      ∫ x, φ (affineCubeTuple (fun j => (c j : ℝ) / L j)
        (fun j => (step j : ℝ) * ((H j : ℝ) - 1) / L j) x) ∂scalarCubeProductMeasure J I| ≤
      (2 * A * scalarCubeGridBoundaryConstant I / volume.real (scalarCubeDomain I) + K * 2) *
        ∑ j, (M j : ℝ) / H j + K * ε := by
  sorry

end Erdos3

end

end OAI
end
