-- Prove2me | Theorems.Thm_OAI_Erdos3_VectorPolynomial_ActualFixedSpatialSlicedForecastPath_density_uniform_budget_s2
-- name    : OAI.Erdos3.VectorPolynomial.ActualFixedSpatialSlicedForecastPath.density_uniform_budget_s2
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-18T05:29:10.212493+00:00
-- url     : https://prove2.me/theorems/4e55690e-0a1b-4333-89c9-6d9fd9230a02
-- title:
--   The sliced forecast density's cap and Lipschitz constant fit the smooth budget
-- statement:
--   Fix the data of OpenAI's actual fixed-spatial forecast setting: a natural number $m$; a finite type $G$; finite types $I_j$ ($j \in \mathrm{Fin}\,m$) and $n : \mathrm{Fin}\,m \to \mathbb N$; finite types $B_a$ for $a \in$ `LayerSamplerAxis I n` (the sigma type $\Sigma_j\, I_j \oplus \mathrm{Fin}(n_j)$); finite types $J_j$, real subspaces $U_j \le \mathbb R^{J_j}$ and bases $b_j$ (indexed by $\mathrm{Fin}(n_j)$) of the orthogonal complement of `euclideanSubspace (U j)`; reals $R_j, \sigma_j$, a `LayerSamplerScale` $S$ for $(B, U, b, R, \sigma)$ over $G$ (a structure bundling a positive natural number $S.\mathrm{value}$ with width and gap inequalities), and proofs $hR$, $h\sigma$ that $R_j > 0$ and $\sigma_j > 0$ for all $j$; a finite type $X$ with decidable equality; finite types $E_j$ (`Eout`); natural numbers $D_{\mathrm{mod}}$ and $L$; embeddings $\mathrm{spatial} : \mathrm{Fin}\,L \hookrightarrow G$, $\mathrm{kernel}_j : \mathrm{Fin}\,L \times \mathrm{Fin}(j+1) \hookrightarrow G$, and $\mathrm{block}_{j,a} : \mathrm{Fin}\,L \hookrightarrow B_{\langle j, a\rangle}$ for every axis $a$ of layer $j$ that is not short (`AllocatedDegreeActiveAxis short j`, where $\mathrm{short}$ is the predicate `allocatedShortAxis U b S.value`, true exactly of the axes $\langle j, \mathrm{inr}\ i\rangle$ with `basisAxisScale (b j) i` $\le S.\mathrm{value}^{j+1}$); a finite type $T$ and an equivalence $G \simeq X \oplus (X \oplus T)$; reals $W_{\mathrm{sp}}, L_{\mathrm{sp}}$; $N : X \to \mathbb N$ (`physicalN`); and reals $\tau, \delta_{\mathrm{slice}}, P, P_{\mathrm{bad}}, P_{\mathrm{pres}}$. Let `slice` be an `ActualFixedSpatialSlicedForecastPath` over these data (a structure bundling an `ActualFixedSpatialForecastPath` `slice.path` over the same data with a step $> 0$, kernel lengths and starts, principal lengths, steps and starts, and identities tying them to the path).
--
--   Assume $|B_a| \ge 4$ for every axis $a$ that is not short (hypothesis `hBactive`), $P \ge 1$, $\delta_{\mathrm{slice}} > 0$, $\delta_{\mathrm{slice}}^{-1} \le e^P$, $|X| \le P$, $|$`LayerSamplerAxis I n`$| \le P$ and $\sum_a |B_a| \le P$. Let $v \ge 0$ be real with $e^{-v} \le$ `slice.kernelWidth g` for every $g \in G$, where `slice.kernelWidth g` $= \mathrm{step} \cdot (\mathrm{kernelLength}(g) - 1)/S.\mathrm{value}$. Put $P_s = P + (|X| + 1) v$ and $\beta = \exp(\mathrm{forecastOriginalSmoothBudget}(m, P_s))$, where `forecastOriginalSmoothBudget m P` $= (10m + 30)(P+1)^2$. Then: `fixedSpatialOriginalForecastCap B (slice.slicedBlockEquiv true) hδslice` $+ 1 \le \beta$; `fixedSpatialOriginalForecastLip B (slice.slicedBlockEquiv false) (slice.slicedBlockEquiv true) hδslice` $\le \beta$; $\|$`slice.density hBactive y`$\| \le \beta$ for every $y$; and `slice.density hBactive` is Lipschitz with constant $\beta$. Here `slice.density hBactive` is a real function (defined by OpenAI as a `fixedSpatialKernelSliceOriginalForecastDensity` of the slice's data) on pairs of a real function on $\Sigma_{x \in X} (\mathrm{Unit} \oplus \mathrm{Empty})$ and a real function on $\Sigma_{a\ \text{not short}} \mathrm{Unit}$; `slice.slicedBlockEquiv second` is a continuous linear automorphism of $\mathbb R^X$ for each boolean `second`; and the cap and Lipschitz constant are nonnegative reals defined by OpenAI from these automorphisms, $B$ and $\delta_{\mathrm{slice}}$.
--
--   Lean: `OAI.Erdos3.VectorPolynomial.ActualFixedSpatialSlicedForecastPath.density_uniform_budget_s2`, which states OpenAI's `OAI.Erdos3.VectorPolynomial.ActualFixedSpatialSlicedForecastPath.density_uniform_budget` (in `lean/OAI/Combinatorics/Progressions/Probability/ActualFixedSpatialSlicedDensityBounds.lean`); the definitions it uses are in the definitions bundle `OAIE3v2B245` of version 2 of this split (and the bundles they import).
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/Progressions/Probability/ActualFixedSpatialSlicedDensityBounds.lean (declaration OAI.Erdos3.VectorPolynomial.ActualFixedSpatialSlicedForecastPath.density_uniform_budget)

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIE3v2B245

section

namespace OAI

section

namespace Erdos3.VectorPolynomial
open MeasureTheory
open scoped BigOperators NNReal Matrix

variable {m : ℕ} {G : Type} [Fintype G]
variable {I : Fin m → Type} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type) [∀ a, Fintype (B a)]
variable {J : Fin m → Type} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
variable (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable {X : Type} [Fintype X] [decX : DecidableEq X]
variable {Eout : Fin m → Type} [∀ j, Fintype (Eout j)]
variable (Dmod : ℕ) {Lrank : ℕ}
variable (spatial : Fin Lrank ↪ G)
variable (kernel : ∀ j : Fin m, Fin Lrank × Fin (j.val + 1) ↪ G)
variable (block : ∀ j, ∀ a : AllocatedDegreeActiveAxis
  (allocatedShortAxis (I := I) U b S.value) j, Fin Lrank ↪ B ⟨j,a.val⟩)
variable {Tsp : Type} [Fintype Tsp]
variable (spatialEquiv : G ≃ X ⊕ (X ⊕ Tsp)) (Wsp Lsp : ℝ)
variable (physicalN : X → ℕ) (τ δslice P Pbad Ppres : ℝ)

namespace ActualFixedSpatialSlicedForecastPath
variable {B U b S hR hσ Dmod spatial kernel block spatialEquiv Wsp Lsp physicalN τ δslice P Pbad Ppres}
variable (slice : ActualFixedSpatialSlicedForecastPath (Eout := Eout) B U b S hR hσ
  Dmod spatial kernel block spatialEquiv Wsp Lsp physicalN τ δslice P Pbad Ppres)

theorem density_uniform_budget_s2
    (hBactive : ∀ a : {a : LayerSamplerAxis I n // ¬allocatedShortAxis U b S.value a},
      4 ≤ Fintype.card (B a.val))
    (hP : 1 ≤ P) (hδslice : 0 < δslice) (hδinv : δslice⁻¹ ≤ Real.exp P)
    (hX : (Fintype.card X : ℝ) ≤ P)
    (haxes : (Fintype.card (LayerSamplerAxis I n) : ℝ) ≤ P)
    (hblocks : (∑ a, (Fintype.card (B a) : ℝ)) ≤ P)
    {v : ℝ} (hv : 0 ≤ v) (hwidth : ∀ g, Real.exp (-v) ≤ slice.kernelWidth g) :
    let Ps := P + (Fintype.card X + 1) * v
    (fixedSpatialOriginalForecastCap B (slice.slicedBlockEquiv true) hδslice : ℝ) + 1 ≤
        Real.exp (forecastOriginalSmoothBudget m Ps) ∧
      (fixedSpatialOriginalForecastLip B (slice.slicedBlockEquiv false)
        (slice.slicedBlockEquiv true) hδslice : ℝ) ≤ Real.exp (forecastOriginalSmoothBudget m Ps) ∧
      (∀ y, ‖slice.density hBactive y‖ ≤ Real.exp (forecastOriginalSmoothBudget m Ps)) ∧
      LipschitzWith (Real.toNNReal (Real.exp (forecastOriginalSmoothBudget m Ps)))
        (slice.density hBactive) := by
  sorry

end ActualFixedSpatialSlicedForecastPath
end Erdos3.VectorPolynomial

end

end OAI
end
