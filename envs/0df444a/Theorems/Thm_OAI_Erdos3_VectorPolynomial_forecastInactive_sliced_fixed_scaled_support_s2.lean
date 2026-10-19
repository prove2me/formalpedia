-- Prove2me | Theorems.Thm_OAI_Erdos3_VectorPolynomial_forecastInactive_sliced_fixed_scaled_support_s2
-- name    : OAI.Erdos3.VectorPolynomial.forecastInactive_sliced_fixed_scaled_support_s2
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-18T04:30:27.822705+00:00
-- url     : https://prove2.me/theorems/29697a9c-45e6-441a-a8ea-13bd3dfd6caa
-- title:
--   Support bound for the supported sliced residue jet law on a grid integer axis with a constant shift
-- statement:
--   Let $m$ be a natural number, $G$ a finite type, $I_j$ ($j \in \operatorname{Fin} m$) finite types with decidable equality, $n : \operatorname{Fin} m \to \mathbb{N}$, and $B$ an assignment of a finite type with decidable equality to each axis of `LayerSamplerAxis I n` (pairs $(j, a)$, $a \in I_j \sqcup \operatorname{Fin} n_j$; the degree of $(j, \cdot)$ is $j+1$). Let $J_j$ be finite types, $U_j$ a real subspace of $J_j \to \mathbb{R}$, $b_j$ a real basis indexed by $\operatorname{Fin} n_j$ of the orthogonal complement of `euclideanSubspace (U j)` (the subspace $U_j$ inside $\mathbb{R}^{J_j}$), $R, \sigma : \operatorname{Fin} m \to \mathbb{R}$ with $R_j > 0$ and $\sigma_j > 0$ for all $j$, and $S$ a `LayerSamplerScale B U b R σ` (OpenAI's structure with a positive natural number `S.value`). Let $\alpha$ be a finite type with decidable equality, $q$ a natural number, and $r$ assign to each triple of `PrincipalTupleIndex B (layerSamplerDegree I n)` and each element of $\operatorname{Option} \alpha$ a residue in $\mathbb{Z}/q$. Let $H, \mathrm{step}$ (natural numbers) and $\mathrm{lower}$ (integers) be functions on the triples, with $H > 0$ and each progression $\{\mathrm{lower}(t) + \mathrm{step}(t)\, k : 0 \le k < H(t)\}$ contained in $[0, \texttt{allocatedPrincipalSides B U b S t})$, and assume the `principalTupleWeights B (layerSamplerDegree I n) H hH` mass of the set of tuples $y$ with `principalResidueLabel q y` $= r$ is positive (hcell). (All named objects are defined by OpenAI.)
--
--   Let $j \in \operatorname{Fin} m$ and $i \in \operatorname{Fin} n_j$, with $\sigma_j \le 1$, and assume the axis $(j, \mathrm{inr}\ i)$ is a grid axis, i.e. satisfies `allocatedGridAxis U b S.value`. Let $\mathrm{rows}$ be a finite set of subsets of $\alpha$, and let $c \in \mathbb{Z}$ have nonzero probability under the PMF `allocatedLayerIntegerPMFs B U b hR hσ S j i e₀` on $\mathbb{Z}$, where $e_0$ = `principalCoefficientChoice (layerSamplerDegree I n) ⟨j, inr i⟩ none` is the constant coefficient slot. Let $z : \mathrm{rows} \to \mathbb{Z}$ have nonzero probability under `allocatedSupportedSlicedResidueJetPMF B U b hR hσ S q r H step lower hH hsubset hcell j i rows sh`, where the shift $\mathrm{sh}(t)$ = `booleanCoefficient (fun _ => c) t` $= \sum_{u \subseteq t} (-1)^{\#(t \setminus u)} c$ (OpenAI's law: draw the principal coefficients of the axis from the allocated layer integer PMFs, draw the cube data from a conditioned law, and output the shift plus the sum of coefficient times integer Boolean block jets). Then for every $t \in \mathrm{rows}$,
--   $$\left| \frac{z(t)}{\texttt{basisAxisScale (b j) i}} \right| \le \#\mathrm{Slots} \cdot \bigl(2^{\#\alpha} (\#\alpha + 1)^{j+1}\bigr) \cdot R_j,$$
--   where `basisAxisScale (b j) i` $= \lceil \|b_{j,i}\|^{-1} \rceil$ and $\mathrm{Slots}$ = `BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j+1)` (exponent vectors of total degree at most $j+1$ on the sampler variables).
--
--   Lean: `OAI.Erdos3.VectorPolynomial.forecastInactive_sliced_fixed_scaled_support_s2`, which states OpenAI's `OAI.Erdos3.VectorPolynomial.forecastInactive_sliced_fixed_scaled_support` (in `lean/OAI/Combinatorics/Progressions/Sampling/ForecastInactiveSlicedFixedAxisCap.lean`); the definitions it uses are in the definitions bundle `OAIE3v2B196` of version 2 of this split (and the bundles they import).
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/Progressions/Sampling/ForecastInactiveSlicedFixedAxisCap.lean (declaration OAI.Erdos3.VectorPolynomial.forecastInactive_sliced_fixed_scaled_support)

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
variable (q : ℕ) (r : PrincipalTupleIndex B (layerSamplerDegree I n) → Option α → ZMod q)
variable (H step : PrincipalTupleIndex B (layerSamplerDegree I n) → ℕ)
variable (lower : PrincipalTupleIndex B (layerSamplerDegree I n) → ℤ) (hH : ∀ t, 0 < H t)
variable (hsubset : ∀ t, integerProgressionSupport (lower t) (step t : ℤ) (H t) ⊆
  Finset.Ico (0 : ℤ) (allocatedPrincipalSides B U b S t : ℤ))
variable (hcell : 0 < (principalTupleWeights (α := α) B (layerSamplerDegree I n) H hH).mass
  (Finset.univ.filter (fun y => principalResidueLabel q y = r)))
variable (j : Fin m) (i : Fin (n j))

local notation "degree" => j.val + 1
local notation "Slots" => BoundedCoefficientExponent (LayerSamplerVariables G I n B) degree
local notation "radius" => (Fintype.card Slots : ℝ) *
  ((2 : ℝ) ^ Fintype.card α * ((Fintype.card α : ℝ) + 1) ^ degree) *
    R j
local notation "scale" => basisAxisScale (b j) i
local notation "constantLaw" => allocatedLayerIntegerPMFs B U b hR hσ S j i
  (principalCoefficientChoice (G := G) (layerSamplerDegree I n) (Sigma.mk j (Sum.inr i)) none)

theorem forecastInactive_sliced_fixed_scaled_support_s2
    (hσ1 : σ j ≤ 1) (hgrid : allocatedGridAxis (I := I) U b S.value ⟨j, Sum.inr i⟩)
    (rows : Finset (Finset α)) (c : ℤ) (hc : constantLaw c ≠ 0) (z : rows → ℤ)
    (hz : allocatedSupportedSlicedResidueJetPMF B U b hR hσ S q r H step lower hH hsubset hcell j i rows
      (fun t => booleanCoefficient (fun _ : Finset α => c) t) z ≠ 0)
    (t : rows) : |(z t : ℝ) / scale| ≤ radius := by
  sorry

end Erdos3.VectorPolynomial

end

end OAI
end
