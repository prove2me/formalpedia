-- Prove2me | Theorems.Thm_OAI_Erdos3_VectorPolynomial_AllocatedSourceNumerics_shared_width_canonical_spatial_choices
-- name    : OAI.Erdos3.VectorPolynomial.AllocatedSourceNumerics.shared_width_canonical_spatial_choices
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-10-10T01:03:11.518362+00:00
-- url     : https://prove2.me/theorems/0834e457-45d0-4ab8-bbea-90f4f71cfddd
-- title:
--   Allocated source numerics give canonical shared-width spatial parameters
-- statement:
--   Fix $m \in \mathbb N$, a finite type $G$, finite types $I_j$ ($j \in \mathrm{Fin}\,m$), $n : \mathrm{Fin}\,m \to \mathbb N$, finite types $B_a$ indexed by $a \in$ `LayerSamplerAxis I n` (the sigma type $\Sigma_j\, I_j \oplus \mathrm{Fin}(n_j)$), finite types $J_j$ with subspaces $U_j \le \mathbb R^{J_j}$, bases $b_j$ (indexed by $\mathrm{Fin}(n_j)$) of the orthogonal complement of `euclideanSubspace (U j)`, reals $R_j, \sigma_j$, a `LayerSamplerScale` $S$ (a structure bundling a positive natural number $S.\mathrm{value}$ with width and gap inequalities), and nonnegative reals $C_j, V_j$. Write $\mathcal T$ for `PrincipalTupleIndex B (layerSamplerDegree I n)` and $\mathcal V$ for `LayerSamplerVariables G I n B`. Let $P$ be a real with `AllocatedSourceNumerics B U b S C V P` (a structure of inequalities bounding $m$, $|\mathcal V|$, coefficient and axis counts by $P$ and $S.\mathrm{value}$, $R_j^{-1}$, $\sigma_j^{-1}$, $C_j$, $V_j$ and other quantities by $\exp P$); assume $R_j > 0$ and $\sigma_j > 0$ for all $j$. Let $X$ be a finite type, $\mathrm{dim}, M \in \mathbb N$, $\mathrm{selection} : \mathrm{Fin}(\mathrm{dim}) \hookrightarrow G$, and reals $p, \mathrm{target}, E_{\mathrm{cap}}, Q_{\mathrm{stride}}, E_\tau, \mathrm{earlyMesh}, \xi, B_\xi$ with $p, \mathrm{target}, E_{\mathrm{cap}}, Q_{\mathrm{stride}}, E_\tau \ge 0$, $M > 0$, $m+1 \le p$, $\mathrm{dim}+1 \le p$, $|G| \le p$, $|X| \le p$, $M \le \exp p$, $0 < \xi \le$ `normalizedTupleNarrowWidth X 𝒯 selection M p target`, $\xi^{-1} \le \exp B_\xi$, $|\mathcal V| \le \exp p$, and $0 < \mathrm{earlyMesh}$. Let $\mathrm{stride}, N : X \to \mathbb N$ with $\mathrm{stride}(i) > 0$ and $\mathrm{stride}(i) \le \exp Q_{\mathrm{stride}}$ for all $i$; let $\tau > 0$ with $\tau^{-1} \le \exp E_\tau$; and assume $\exp($`sharedWidthNormalizedTupleSideLog X 𝒯 selection p target ℓ Bξ`$) \le N(i)$ for all $i$, where $\ell =$ `allocatedSpatialLateLog B P P` $+ E_{\mathrm{cap}} + Q_{\mathrm{stride}} + E_\tau$. Put $W =$ `allocatedPhysicalRootBudget B U b S 0` (a real), $C_0 = 1 + S.\mathrm{value} + W$, $C_{\mathrm{entry}} =$ `allocatedPhysicalEntryBudget B U b S 0`, $\delta =$ `normalizedTupleRadius X selection M p target W`, $\rho =$ `normalizedTupleResolution X 𝒯 selection M p target C₀ W (exp Ecap) Centry`, and $\mathrm{mesh} = \min(\delta/4, \mathrm{earlyMesh})$; write $\lambda$ for the constant `probabilityProfileLipschitz` and $\varsigma$ for `normalizedSpatialShare target` $= e^{-(\mathrm{target}+2)}$. Then all of the following hold: $0 \le W$; $1 \le C_0$; $S.\mathrm{value} \le C_0$; $W \le C_0$; $W \le |\mathcal V|\,S.\mathrm{value}$; $0 < \xi \le 1$; $0 < \delta \le 1$; $0 < \rho$; $0 < \mathrm{mesh}$, $\mathrm{mesh} \le \mathrm{earlyMesh}$, $\mathrm{mesh} \le \delta/4$; $8(1+W)\,\mathrm{stride}(i)\,\rho \le \xi\tau N(i)$ for all $i$; `anisotropicSpatialMeshThreshold selection 𝒯 C₀` $\le \rho$; $8\lambda \le \rho$; $2\,|\mathrm{Option}\,\mathcal V|\,(2C_{\mathrm{entry}}) \le \rho$; $|\mathcal T|\,(2C_{\mathrm{entry}}) \le \delta\rho$; $\exp(E_{\mathrm{cap}})\,\bigl(24\lambda\,|\mathrm{Option}\,\mathcal V \times X| / \rho\bigr) \le \varsigma/2$; for every $\mathrm{period} \in \mathbb N$ with $\mathrm{period} \le M^{m+1}$, `allocatedTupleSpatialError |X| selection 𝒯 M period C₀ ρ ξ W δ mesh` $\cdot$ `coarseReferenceMassConstant dim X W S.value` $\le \varsigma/2$; and, with widths $=$ `narrowTrimmedSpatialWidths W τ ξ N` (a real function on $\mathrm{Option}(G \oplus \mathcal T) \times X$), $N(i) > 0$ for all $i$, $\mathrm{widths}(z) > 0$ for all $z$, and for every nonempty finite set cells of `ColumnResiduePattern (Option 𝒱) X stride` (functions assigning to each $(k, i)$ an element of $\mathbb Z/\mathrm{stride}(i)$), $0 < \sum'_z$ `selectedResidueSmoothWeight stride cells widths z` (a `tsum` over $z : \mathrm{Option}\,\mathcal V \times X \to \mathbb Z$).
--
--   Lean: `OAI.Erdos3.VectorPolynomial.AllocatedSourceNumerics.shared_width_canonical_spatial_choices` in `lean/OAI/Combinatorics/Progressions/Geometry/SharedWidthAllocatedCanonicalSpatialNativeSource.lean` (OpenAI); the definitions it uses are in the definitions bundles `OAIErdos3B054`, `OAIErdos3B144`, `OAIErdos3B149` of this split (and the bundles they import).
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/Progressions/Geometry/SharedWidthAllocatedCanonicalSpatialNativeSource.lean#L121

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIErdos3B054
import Definitions.Def_OAIErdos3B131
import Definitions.Def_OAIErdos3B171
import Definitions.Def_OAIErdos3B172

namespace OAI

section

namespace Erdos3

open BooleanCubeKernel VectorPolynomial
open scoped NNReal

end Erdos3

end

section

namespace Erdos3.VectorPolynomial

open BooleanCubeKernel
open scoped NNReal

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
variable (C V : Fin m → ℝ≥0)

theorem AllocatedSourceNumerics.shared_width_canonical_spatial_choices
    {P : ℝ} (hnum : AllocatedSourceNumerics B U b S C V P)
    (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
    {X : Type*} [Fintype X] {dim M : ℕ} (selection : Fin dim ↪ G)
    {p target Ecap Qstride Etau earlyMesh ξ Bξ : ℝ}
    (hp : 0 ≤ p) (htarget : 0 ≤ target)
    (hEcap : 0 ≤ Ecap) (hQstride : 0 ≤ Qstride) (hEtau : 0 ≤ Etau)
    (hM : 0 < M) (hm : ((m + 1 : ℕ) : ℝ) ≤ p)
    (hdim : ((dim + 1 : ℕ) : ℝ) ≤ p)
    (hG : (Fintype.card G : ℝ) ≤ p) (hX : (Fintype.card X : ℝ) ≤ p)
    (hMp : (M : ℝ) ≤ Real.exp p)
    (hξ : 0 < ξ)
    (hξle : ξ ≤ normalizedTupleNarrowWidth X
      (PrincipalTupleIndex B (layerSamplerDegree I n)) selection M p target)
    (hξB : ξ⁻¹ ≤ Real.exp Bξ)
    (hvars : (Fintype.card (LayerSamplerVariables G I n B) : ℝ) ≤ Real.exp p)
    (hearlyMesh : 0 < earlyMesh)
    (stride N : X → ℕ) (hstridepos : ∀ i, 0 < stride i)
    (hstride : ∀ i, (stride i : ℝ) ≤ Real.exp Qstride)
    {τ : ℝ} (hτ : 0 < τ) (hτinv : τ⁻¹ ≤ Real.exp Etau)
    (hside : ∀ i, Real.exp (sharedWidthNormalizedTupleSideLog X
      (PrincipalTupleIndex B (layerSamplerDegree I n)) selection p target
      (allocatedSpatialLateLog (G := G) B P P + Ecap + Qstride + Etau) Bξ) ≤ (N i : ℝ)) :
    let W := allocatedPhysicalRootBudget B U b S (fun _ => 0)
    let C₀ := 1 + (S.value : ℝ) + W
    let Centry := allocatedPhysicalEntryBudget B U b S (fun _ => 0)
    let δ := normalizedTupleRadius X selection M p target W
    let ρ := normalizedTupleResolution X (PrincipalTupleIndex B (layerSamplerDegree I n))
      selection M p target C₀ W (Real.exp Ecap) Centry
    let mesh := min (δ / 4) earlyMesh
    0 ≤ W ∧ 1 ≤ C₀ ∧ (S.value : ℝ) ≤ C₀ ∧ W ≤ C₀ ∧
    W ≤ Fintype.card (LayerSamplerVariables G I n B) * (S.value : ℝ) ∧
    0 < ξ ∧ ξ ≤ 1 ∧ 0 < δ ∧ δ ≤ 1 ∧ 0 < ρ ∧
    0 < mesh ∧ mesh ≤ earlyMesh ∧ mesh ≤ δ / 4 ∧
    (∀ i, 8 * (1 + W) * (stride i : ℝ) * ρ ≤ (ξ * τ) * (N i : ℝ)) ∧
    anisotropicSpatialMeshThreshold selection (PrincipalTupleIndex B (layerSamplerDegree I n)) C₀ ≤ ρ ∧
    8 * probabilityProfileLipschitz ≤ ρ ∧
    2 * (Fintype.card (Option (LayerSamplerVariables G I n B)) * (2 * Centry)) ≤ ρ ∧
    Fintype.card (PrincipalTupleIndex B (layerSamplerDegree I n)) * (2 * Centry) ≤ δ * ρ ∧
    Real.exp Ecap * (24 * probabilityProfileLipschitz *
      Fintype.card (Option (LayerSamplerVariables G I n B) × X) / ρ) ≤ normalizedSpatialShare target / 2 ∧
    (∀ period : ℕ, period ≤ M ^ (m + 1) →
      allocatedTupleSpatialError (Fintype.card X) selection
        (PrincipalTupleIndex B (layerSamplerDegree I n)) M period C₀ ρ ξ W δ mesh *
        coarseReferenceMassConstant dim X W S.value ≤ normalizedSpatialShare target / 2) ∧
    let widths := narrowTrimmedSpatialWidths (G := G)
      (J := PrincipalTupleIndex B (layerSamplerDegree I n)) W τ ξ N
    (∀ i, 0 < N i) ∧ (∀ z, 0 < widths z) ∧
    ∀ cells : Finset (ColumnResiduePattern (Option (LayerSamplerVariables G I n B)) X stride),
      cells.Nonempty → 0 < ∑' z, selectedResidueSmoothWeight stride cells widths z := by
  sorry

end Erdos3.VectorPolynomial
end
end OAI
