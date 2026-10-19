-- Prove2me | Theorems.Thm_OAI_Erdos3_VectorPolynomial_allocatedSupportedSlicedFullGridNaturalSite_error_s2
-- name    : OAI.Erdos3.VectorPolynomial.allocatedSupportedSlicedFullGridNaturalSite_error_s2
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-18T04:36:26.090981+00:00
-- url     : https://prove2.me/theorems/34b3ab40-3fc5-485c-a917-1a6ab8c9e818
-- title:
--   Axiswise site expansions that approximate the sliced physical grid laws give a δ-approximation of the full-grid supported sliced density
-- statement:
--   **Setting.** Let $m \in \mathbb{N}$; let $G$ be a finite type; let $I_j$ ($j \in \mathrm{Fin}\,m$) be finite types with decidable equality, $n : \mathrm{Fin}\,m \to \mathbb{N}$, and $B_a$ finite types with decidable equality indexed by the sampler axes $a$ in `LayerSamplerAxis I n`; let $J_j$ be finite types, $U_j \subseteq \mathbb{R}^{J_j}$ subspaces, and $b_j$ a basis, indexed by $\mathrm{Fin}(n_j)$, of the orthogonal complement of $U_j$; let $R, \sigma : \mathrm{Fin}\,m \to \mathbb{R}$ with $R_j > 0$ and $\sigma_j > 0$ for all $j$, and $S$ a `LayerSamplerScale B U b R σ` (a structure defined by OpenAI). Let $\alpha$ be a finite type with decidable equality and $\mathrm{rowSets} : \mathrm{Fin}\,m \to \mathrm{Finset}(\mathrm{Finset}\,\alpha)$. The grid axes are the sampler axes $a$ with `allocatedGridAxis U b S.value a` (defined by OpenAI); for a grid axis $a$, $\mathrm{ig}(a) = (j_a, i_a)$ with $i_a \in \mathrm{Fin}(n_{j_a})$ is its integer-axis label (`allocatedGridIntegerAxis`) and $N_a$ = `allocatedGridNaturalScale B U b S a` is a natural number defined by OpenAI.
--
--   Let $H, \mathrm{step} : \mathrm{Tuple} \to \mathbb{N}$ and $c : \mathrm{Tuple} \to \mathbb{Z}$, where $\mathrm{Tuple}$ = `PrincipalTupleIndex B (layerSamplerDegree I n)`, with $H_t > 0$ for all $t$ and, for every $t$, the progression $\{c_t + \mathrm{step}_t\, k : 0 \le k < H_t\}$ contained in $[0, \texttt{allocatedPrincipalSides B U b S}\ t)$. Let $q \in \mathbb{N}$ and $r : \mathrm{Tuple} \to \mathrm{Option}\,\alpha \to \mathbb{Z}/q$, and assume (hypothesis $h_{\mathrm{cell}}$) that the residue cell $\{y : y_{t,i} \bmod q = r_{t,i} \text{ for all } t, i\}$ has positive mass under `principalTupleWeights B (layerSamplerDegree I n) H` (the product over $t$ of the integer scalar cube laws of side $H_t$, defined by OpenAI).
--
--   For a grid axis $a$, $x : G \to$ `IntegerScalarCubeBox α S.value` and an integer point $z$, write $\Pi_a(x, z)$ for the real number `(allocatedSupportedSlicedPhysicalGridPMF B U b hR hσ S q r H step c hH hsubset hcell j_a i_a (rowSets j_a) x z).toReal` (a probability mass function defined by OpenAI).
--
--   **Statement.** Let $e$ assign to each grid axis a `ScalarSiteExpansion` over $\mathrm{Finset}\,\alpha$ (in the universe of $\alpha$; defined by OpenAI), and let $C, \delta$ be reals with $0 \le C$ and $0 < \delta$. Assume:
--   - for every grid axis $a$, every $x$ and every $z$: $N_a^{|\mathrm{rowSets}_{j_a}|} \cdot \Pi_a(x, z) \le C$ (in absolute value);
--   - for every grid axis $a$, every $x$ and every $y : \mathrm{Finset}\,\alpha \to \mathbb{Z}$ whose Boolean (Möbius) coefficients $\hat y(t) = \sum_{t' \subseteq t} (-1)^{|t \setminus t'|} y(t')$ vanish for all $t \notin \mathrm{rowSets}_{j_a}$:
--   $$\Bigl| N_a^{|\mathrm{rowSets}_{j_a}|} \cdot \Pi_a(x, \hat y) - \texttt{(e a).integerEval}\ N_a\ y \Bigr| \le \texttt{uniformProductAccuracy}\ (\#\mathrm{grid\ axes})\ C\ \delta,$$
--   where `(e a).integerEval N y` is the expansion $e_a$ evaluated at $y$ and at the real point $y/N$, and `uniformProductAccuracy k C δ` $= \min\bigl(1, \delta / ((k+1)(C+2)^k)\bigr)$ (both defined by OpenAI).
--
--   Then for every $x : G \to$ `IntegerScalarCubeBox α S.value` and every $z$ in `AllocatedFrozenJetRows B U b S rowTypes` (with $\mathrm{rowTypes}_j$ the subtype of $\mathrm{rowSets}_j$),
--   $$\Bigl| V \cdot \texttt{allocatedSupportedSlicedFullGridDensity B U b hR hσ S rowSets H step c hH hsubset q r hcell}\ x\ z \;-\; \texttt{allocatedFullGridSiteApproximation B U b S rowSets e}\ z \Bigr| \le \delta,$$
--   where $V$ = `allocatedFullGridNaturalVolume B U b S rowSets`; all three are defined by OpenAI.
--
--   Lean: `OAI.Erdos3.VectorPolynomial.allocatedSupportedSlicedFullGridNaturalSite_error_s2`, which states OpenAI's `OAI.Erdos3.VectorPolynomial.allocatedSupportedSlicedFullGridNaturalSite_error` (in `lean/OAI/Combinatorics/Progressions/Geometry/AllocatedSupportedSlicedNaturalSiteError.lean`); the definitions it uses are in the definitions bundles `OAIE3v2B195`, `OAIE3v2B196` of version 2 of this split (and the bundles they import).
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/Progressions/Geometry/AllocatedSupportedSlicedNaturalSiteError.lean (declaration OAI.Erdos3.VectorPolynomial.allocatedSupportedSlicedFullGridNaturalSite_error)

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIE3v2B195
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

local notation "gridAxes" => {a // allocatedGridAxis (I := I) U b S.value a}
local notation "ig" => allocatedGridIntegerAxis B U b S
local notation "axisN" => allocatedGridNaturalScale B U b S
local notation "rowTypes" => (fun j : Fin m => {t : Finset α // t ∈ rowSets j})

variable (H step : PrincipalTupleIndex B (layerSamplerDegree I n) → ℕ)
variable (c : PrincipalTupleIndex B (layerSamplerDegree I n) → ℤ) (hH : ∀ j, 0 < H j)
variable (hsubset : ∀ j, integerProgressionSupport (c j) (step j : ℤ) (H j) ⊆
  Finset.Ico (0 : ℤ) (allocatedPrincipalSides B U b S j : ℤ))
variable (q : ℕ) (r : PrincipalTupleIndex B (layerSamplerDegree I n) → Option α → ZMod q)
variable (hcell : 0 < (principalTupleWeights (α := α) B (layerSamplerDegree I n) H hH).mass
  (Finset.univ.filter (fun y => principalResidueLabel q y = r)))

theorem allocatedSupportedSlicedFullGridNaturalSite_error_s2
    (e : gridAxes → ScalarSiteExpansion.{uα,uα} (Finset α)) {C δ : ℝ} (hC : 0 ≤ C) (hδ : 0 < δ)
    (hcap : ∀ a (x : G → IntegerScalarCubeBox α S.value) z,
      ‖(((axisN a : ℝ) ^ (rowSets (ig a).1).card *
        (allocatedSupportedSlicedPhysicalGridPMF B U b hR hσ S q r H step c hH hsubset hcell
          (ig a).1 (ig a).2 (rowSets (ig a).1) x z).toReal : ℝ) : ℂ)‖ ≤ C)
    (he : ∀ a (x : G → IntegerScalarCubeBox α S.value) (y : Finset α → ℤ),
      (∀ t ∉ rowSets (ig a).1, booleanCoefficient y t = 0) →
      ‖(((axisN a : ℝ) ^ (rowSets (ig a).1).card *
        (allocatedSupportedSlicedPhysicalGridPMF B U b hR hσ S q r H step c hH hsubset hcell
          (ig a).1 (ig a).2 (rowSets (ig a).1) x (fun t => booleanCoefficient y t)).toReal : ℝ) : ℂ) -
        (e a).integerEval (axisN a) y‖ ≤ uniformProductAccuracy (Fintype.card gridAxes) C δ)
    (x : G → IntegerScalarCubeBox α S.value) (z : AllocatedFrozenJetRows B U b S rowTypes) :
    ‖(allocatedFullGridNaturalVolume B U b S rowSets : ℂ) *
        (allocatedSupportedSlicedFullGridDensity B U b hR hσ S rowSets H step c hH hsubset q r hcell x z : ℂ) -
      allocatedFullGridSiteApproximation B U b S rowSets e z‖ ≤ δ := by
  sorry

end Erdos3.VectorPolynomial

end

end OAI
end
