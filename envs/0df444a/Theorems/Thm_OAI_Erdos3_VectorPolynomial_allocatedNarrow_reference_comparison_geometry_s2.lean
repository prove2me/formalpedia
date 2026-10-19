-- Prove2me | Theorems.Thm_OAI_Erdos3_VectorPolynomial_allocatedNarrow_reference_comparison_geometry_s2
-- name    : OAI.Erdos3.VectorPolynomial.allocatedNarrow_reference_comparison_geometry_s2
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-17T11:09:25.128246+00:00
-- url     : https://prove2.me/theorems/68aa6f3b-816b-4e74-8d13-1a9aa8952a22
-- title:
--   Row sums of the allocated physical cube matrix are bounded by the trimmed spatial root scale, which is at least 1
-- statement:
--   Let $m \in \mathbb{N}$; let $G$ be a finite type; let $I_j$ ($j \in \mathrm{Fin}\,m$) be finite types, $n : \mathrm{Fin}\,m \to \mathbb{N}$, and $B_a$ finite types indexed by the sampler axes $a$ in `LayerSamplerAxis I n`; let $J_j$ be finite types, $U_j \subseteq \mathbb{R}^{J_j}$ subspaces, and $\mathrm{basis}_j$ a basis, indexed by $\mathrm{Fin}(n_j)$, of the orthogonal complement of $U_j$; let $R, \sigma : \mathrm{Fin}\,m \to \mathbb{R}$ and let $S$ be a `LayerSamplerScale B U basis R σ` (a structure defined by OpenAI, with natural-number value `S.value`). Let $K$ = `LayerSamplerVariables G I n B` (a finite type defined by OpenAI), let $\alpha$ be a type, $c : K \to \mathbb{Z}$, $x : G \to$ `IntegerScalarCubeBox α S.value` (functions $\mathrm{Option}\,\alpha \to [-S.\mathrm{value}, S.\mathrm{value}) \cap \mathbb{Z}$), and $y$ an element of `PrincipalIntegerTuples B (layerSamplerDegree I n) α (allocatedPrincipalSides B U basis S)` (defined by OpenAI).
--
--   Let $X$ be a type and $N, \mathrm{stride} : X \to \mathbb{N}$ with $N_t > 0$ and $\mathrm{stride}_t > 0$ for all $t$. Let $W, \tau, \xi, \rho$ be reals with $0 \le W$, $0 < \tau$, $\xi \le 1$, and assume:
--   - $8(1 + W)\,\mathrm{stride}_t\, \rho \le (\xi \tau)\, N_t$ for every $t \in X$;
--   - $8 \cdot$ `probabilityProfileLipschitz` $\le \rho$, where `probabilityProfileLipschitz` is a fixed Lipschitz constant ($\ge 1$) of a smooth probability profile chosen by OpenAI;
--   - $2 \cdot |\mathrm{Option}\,K| \cdot \bigl(2\,\texttt{allocatedPhysicalEntryBudget B U basis S c}\bigr) \le \rho$, where `allocatedPhysicalEntryBudget B U basis S c` $= 1 + \texttt{allocatedPhysicalRootBudget B U basis S c} + S.\mathrm{value}$ (defined by OpenAI).
--
--   Let $H_t$ = `trimmedSpatialRootScale τ N stride t` $= \tau N_t / 8 / \mathrm{stride}_t$. Let $D$ be the integer matrix `physicalCubeCoefficient root dirs`, with rows indexed by $\mathrm{Unit} \sqcup \alpha$ and columns by $\mathrm{Option}\,K$, where $\mathrm{root}$ = `allocatedPhysicalCubeRoot B U basis S c x y` ($k \mapsto c_k$ plus the $\mathrm{none}$-entry of $x$ or $y$ at $k$) and $\mathrm{dirs}$ = `allocatedPhysicalCubeDirections B U basis S x y` (the $\alpha \times K$ matrix of the $\mathrm{some}\,i$-entries of $x$ or $y$); its first row is $(1, \mathrm{root})$ and the other rows are $(0, \mathrm{dirs}_i)$. Then:
--   1. for every $t \in X$ and every row $i$, $\sum_{k \in \mathrm{Option}\,K} |D_{i,k}| \le H_t$;
--   2. for every $t$, $8 \cdot$ `probabilityProfileLipschitz` $\le 20\, H_t$;
--   3. for every $t$, $1 \le H_t$.
--
--   Lean: `OAI.Erdos3.VectorPolynomial.allocatedNarrow_reference_comparison_geometry_s2`, which states OpenAI's `OAI.Erdos3.VectorPolynomial.allocatedNarrow_reference_comparison_geometry` (in `lean/OAI/Combinatorics/Progressions/Estimates/AllocatedReferenceJetWindow.lean`); the definitions it uses are in the definitions bundle `OAIE3v2B126` of version 2 of this split (and the bundles they import).
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/Progressions/Estimates/AllocatedReferenceJetWindow.lean (declaration OAI.Erdos3.VectorPolynomial.allocatedNarrow_reference_comparison_geometry)

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIE3v2B126

section

namespace OAI

section

namespace Erdos3.VectorPolynomial

open BooleanCubeKernel
open scoped BigOperators

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U basis R σ)
variable {α : Type*} (c : LayerSamplerVariables G I n B → ℤ)
variable (x : G → IntegerScalarCubeBox α S.value)

theorem allocatedNarrow_reference_comparison_geometry_s2
    (y : PrincipalIntegerTuples B (layerSamplerDegree I n) α (allocatedPrincipalSides B U basis S))
    {X : Type*} (N stride : X → ℕ) (hN : ∀ t, 0 < N t) (hs : ∀ t, 0 < stride t)
    {W τ ξ ρ : ℝ} (hW : 0 ≤ W) (hτ : 0 < τ) (hξ1 : ξ ≤ 1)
    (hsize : ∀ t, 8 * (1 + W) * (stride t : ℝ) * ρ ≤ (ξ * τ) * (N t : ℝ))
    (hρ8 : 8 * (probabilityProfileLipschitz : ℝ) ≤ ρ)
    (hρshift : 2 * (Fintype.card (Option (LayerSamplerVariables G I n B)) *
      (2 * allocatedPhysicalEntryBudget B U basis S c)) ≤ ρ) :
    let H := trimmedSpatialRootScale τ N stride
    (∀ t i, (∑ k, |(physicalCubeCoefficient (allocatedPhysicalCubeRoot B U basis S c x y)
      (allocatedPhysicalCubeDirections B U basis S x y) i k : ℝ)|) ≤ H t) ∧
    (∀ t, 8 * (probabilityProfileLipschitz : ℝ) ≤ 20 * H t) ∧
    (∀ t, 1 ≤ H t) := by
  sorry

end Erdos3.VectorPolynomial

end

end OAI
end
