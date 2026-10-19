-- Prove2me | Theorems.Thm_OAI_Erdos3_VectorPolynomial_allocatedSupportedSlicedFullGridDensity_mean_s2
-- name    : OAI.Erdos3.VectorPolynomial.allocatedSupportedSlicedFullGridDensity_mean_s2
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-18T04:27:03.44617+00:00
-- url     : https://prove2.me/theorems/bb2b72bb-083c-4778-aab1-9881fdb85b92
-- title:
--   Averaging the grid jet density over the contained supported progression law gives the supported sliced full-grid density
-- statement:
--   All named objects below are defined by OpenAI.
--
--   Let $m$ be a natural number, $G$ a finite type, $I_j$ ($j<m$) finite types with decidable equality, $n : \mathrm{Fin}(m)\to\mathbb{N}$, $B_a$ finite types with decidable equality indexed by `LayerSamplerAxis I n` $= \Sigma_j (I_j \sqcup \mathrm{Fin}(n_j))$, $J_j$ finite types, $U_j \subseteq \mathbb{R}^{J_j}$ subspaces, `b j` bases (indexed by $\mathrm{Fin}(n_j)$) of the orthogonal complement of `euclideanSubspace (U j)`, $R, \sigma : \mathrm{Fin}(m) \to \mathbb{R}$ with $R_j > 0$ and $\sigma_j > 0$ for all $j$ (these positivity proofs `hR`, `hσ` enter the definitions below), and `S : LayerSamplerScale B U b R σ`. Let $\alpha$ be a finite type with decidable equality, `rowSets j` a finite set of finite subsets of $\alpha$ for each $j$, `rowTypes j` its subtype and `rows j` the inclusion of `rowTypes j` into finite subsets of $\alpha$.
--
--   Write $\mathcal{P}$ = `PrincipalTupleIndex B (layerSamplerDegree I n)` and `sides` = `allocatedPrincipalSides B U b S` (positive natural numbers indexed by $\mathcal{P}$). Let $H, \mathrm{step} : \mathcal{P} \to \mathbb{N}$ and $c : \mathcal{P} \to \mathbb{Z}$ with $H_j > 0$ and, for every $j$, the progression $\{c_j + \mathrm{step}_j\, k : k < H_j\}$ (`integerProgressionSupport`) contained in $[0, \texttt{sides}_j)$. Let $q$ be a natural number and $r : \mathcal{P} \to \mathrm{Option}\ \alpha \to \mathbb{Z}/q\mathbb{Z}$ a residue label, such that the set of tuples $y$ with `principalResidueLabel q y = r` has positive mass under `principalTupleWeights B (layerSamplerDegree I n) H hH` (hypothesis `hcell`). Let `grid` = `allocatedGridAxis U b S.value`, and let `gridLaw` be the finite probability weights `containedSupportedProgressionAxisLaw B (layerSamplerDegree I n) sides H step c (allocatedPrincipalSides_pos B U b S) hH hsubset q r hcell grid` on `PrincipalAxisTuples grid sides` (the law of the grid-axis part of a tuple drawn from the residue-$r$ cell of the contained progressions).
--
--   Then for every $x : G \to$ `IntegerScalarCubeBox α S.value`, every $v_0$ in `PrincipalAxisTuples (fun a => ¬grid a) sides`, and every $z$ in `AllocatedFrozenJetRows B U b S rowTypes`,
--   $$\mathbb{E}_{u \sim \texttt{gridLaw}}\bigl[\texttt{allocatedGridJetDensity B U b hR hσ S x}\ u\ v_0\ \texttt{rows}\ z\bigr] = \texttt{allocatedSupportedSlicedFullGridDensity B U b hR hσ S rowSets H step c hH hsubset q r hcell x}\ z,$$
--   where the left side is the mean under `gridLaw` of OpenAI's product of grid jet factors, and the right side is OpenAI's product, over grid integer axes, of the real values of `allocatedSupportedSlicedPhysicalGridPMF` at the grid integer values of $z$.
--
--   Lean: `OAI.Erdos3.VectorPolynomial.allocatedSupportedSlicedFullGridDensity_mean_s2`, which states OpenAI's `OAI.Erdos3.VectorPolynomial.allocatedSupportedSlicedFullGridDensity_mean` (in `lean/OAI/Combinatorics/Progressions/Sampling/AllocatedClippedFullGridGlobal.lean`); the definitions it uses are in the definitions bundle `OAIE3v2B196` of version 2 of this split (and the bundles they import).
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/Progressions/Sampling/AllocatedClippedFullGridGlobal.lean (declaration OAI.Erdos3.VectorPolynomial.allocatedSupportedSlicedFullGridDensity_mean)

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIE3v2B196

section

namespace OAI

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators Classical NNReal

universe uα

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)] [∀ a, DecidableEq (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U b R σ)
variable {α : Type uα} [Fintype α] [DecidableEq α]
variable (rowSets : Fin m → Finset (Finset α))

local notation "ig" => allocatedGridIntegerAxis B U b S
local notation "rowTypes" => (fun j : Fin m => {t : Finset α // t ∈ rowSets j})
local notation "rows" => (fun j => (Subtype.val : rowSets j → Finset α))

variable (H step : PrincipalTupleIndex B (layerSamplerDegree I n) → ℕ)
variable (c : PrincipalTupleIndex B (layerSamplerDegree I n) → ℤ) (hH : ∀ j, 0 < H j)
variable (hsubset : ∀ j, integerProgressionSupport (c j) (step j : ℤ) (H j) ⊆
  Finset.Ico (0 : ℤ) (allocatedPrincipalSides B U b S j : ℤ))
variable (q : ℕ) (r : PrincipalTupleIndex B (layerSamplerDegree I n) → Option α → ZMod q)
variable (hcell : 0 < (principalTupleWeights (α := α) B (layerSamplerDegree I n) H hH).mass
  (Finset.univ.filter (fun y => principalResidueLabel q y = r)))
local notation "grid" => allocatedGridAxis (I := I) U b S.value
local notation "gridLaw" => containedSupportedProgressionAxisLaw B (layerSamplerDegree I n)
  (allocatedPrincipalSides B U b S) H step c (allocatedPrincipalSides_pos B U b S) hH hsubset q r hcell grid

theorem allocatedSupportedSlicedFullGridDensity_mean_s2 (x : G → IntegerScalarCubeBox α S.value)
    (v₀ : PrincipalAxisTuples (α := α) (fun a => ¬grid a) (allocatedPrincipalSides B U b S))
    (z : AllocatedFrozenJetRows B U b S rowTypes) :
    (gridLaw).mean (fun u => allocatedGridJetDensity B U b hR hσ S x u v₀ rows z) =
      allocatedSupportedSlicedFullGridDensity B U b hR hσ S rowSets H step c hH hsubset q r hcell x z := by
  sorry

end Erdos3.VectorPolynomial

end

end OAI
end
