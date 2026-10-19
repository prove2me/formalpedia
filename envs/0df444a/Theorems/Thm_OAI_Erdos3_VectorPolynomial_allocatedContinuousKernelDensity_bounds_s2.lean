-- Prove2me | Theorems.Thm_OAI_Erdos3_VectorPolynomial_allocatedContinuousKernelDensity_bounds_s2
-- name    : OAI.Erdos3.VectorPolynomial.allocatedContinuousKernelDensity_bounds_s2
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-17T11:43:00.877304+00:00
-- url     : https://prove2.me/theorems/dfd20e29-c916-4706-9b5b-5d0e1fba29ae
-- title:
--   The allocated continuous kernel density is bounded by the pivot kernel cap and Lipschitz on the unit ball
-- statement:
--   **Setting.** Let $m \in \mathbb{N}$; let $G$ be a finite type; let $I_j$ ($j \in \mathrm{Fin}\,m$) be finite types, $n : \mathrm{Fin}\,m \to \mathbb{N}$, and $B_a$ finite types indexed by the sampler axes $a$ in `LayerSamplerAxis I n`; let $J_j$ be finite types, $U_j \subseteq \mathbb{R}^{J_j}$ subspaces, and $\mathrm{basis}_j$ a basis, indexed by $\mathrm{Fin}(n_j)$, of the orthogonal complement of $U_j$. Let $R, \sigma : \mathrm{Fin}\,m \to \mathbb{R}$ with $R_j > 0$ and $\sigma_j > 0$ for all $j$, and let $S$ be a `LayerSamplerScale B U basis R σ` (a structure defined by OpenAI, with a positive natural-number value `S.value`). Fix $j \in \mathrm{Fin}\,m$ and $i \in I_j$. Let $\alpha$ and $O$ be finite types with decidable equality, $x : G \to$ `IntegerScalarCubeBox α S.value` (functions $\mathrm{Option}\,\alpha \to [-S.\mathrm{value}, S.\mathrm{value}) \cap \mathbb{Z}$), $u$ an element of `PrincipalAxisTuples` for the axes outside the grid set `allocatedGridAxis U basis S.value` with sides `allocatedPrincipalSides B U basis S`, $\mathrm{rows} : O \to \mathrm{Finset}\,\alpha$, and $s : O \hookrightarrow$ `BoundedIntegerExponent G (j+1)` an embedding such that the square submatrix (columns selected by $s$) of the integer jet matrix `scalarKernelIntegerJet x (j+1) rows` has nonzero determinant (hypothesis $h_A$). All these objects are defined by OpenAI.
--
--   Let $\mathrm{pivot}$ be the linear automorphism of $\mathbb{R}^O$ given by `normalizedPivotEquiv` of that submatrix, with column scales `kernelJetCoefficientScale G (j+1) S.value 1` (at $s(o)$) and row scales $1$; let $\rho = R_j$ and $\delta$ = `allocatedUnitProfileWidth (R j) (σ j) (|BoundedCoefficientExponent K (j+1)|)` (a positive real defined by OpenAI), where $K$ = `LayerSamplerVariables G I n B`. Let $D_y(v)$ denote `allocatedContinuousKernelDensity B U basis S j i x u rows s h_A y v`, a real-valued density in $v \in \mathbb{R}^O$ depending on a parameter $y$ (a real vector indexed by `PrincipalAxisParameter` of the non-grid axes), defined by OpenAI.
--
--   **Statement.** Assume $\sigma_j \le 1$ and let $v \in \mathbb{R}^O$. Then:
--   1. for every $y$, $|D_y(v)| \le$ `pivotKernelCap (UnselectedColumn s) pivot ρ (δ⁻¹ ^ |BoundedIntegerExponent G (j+1)|)`, where `pivotKernelCap J A R H` $= \operatorname{invJac}(A) \cdot H \cdot (2R)^{|J|}$ (defined by OpenAI, with `inverseJacobian` $\operatorname{invJac}$) and `UnselectedColumn s` is the type of columns not selected by $s$;
--   2. the map $y \mapsto D_y(v)$ is Lipschitz on the closed unit ball (sup norm) around $0$ with constant
--   $$\texttt{pivotKernelLip (UnselectedColumn s) pivot}\ \rho\ (\texttt{affineProductProfileLip}\ (\texttt{BoundedIntegerExponent}\ G\ (j+1))\ \delta) \cdot \bigl(|\texttt{AllocatedNonkernelCoefficient}\ B\ j| \cdot \texttt{polynomialBoxLip}\ N_{\mathrm{par}}\ (j+1)\ (\texttt{normalizedJetMass}\ \alpha\ (j+1))\bigr) \cdot \rho,$$
--   where $N_{\mathrm{par}}$ is the cardinality of `PrincipalAxisParameter` for the non-grid axes, and (definitions by OpenAI) `pivotKernelLip J A R K` $=$ `pivotKernelCap J A R K` $\cdot \|A^{-1}\|$, `affineProductProfileLip I δ` $= |I| \cdot$ `probabilityProfileLipschitz` $\cdot\, \delta^{-(|I|+1)}$, `polynomialBoxLip n d C` $= n\,(d+1)^n\, d\, C$, and `normalizedJetMass α d` $= 2^{|\alpha|} (|\alpha| + 1)^d$.
--
--   Lean: `OAI.Erdos3.VectorPolynomial.allocatedContinuousKernelDensity_bounds_s2`, which states OpenAI's `OAI.Erdos3.VectorPolynomial.allocatedContinuousKernelDensity_bounds` (in `lean/OAI/Combinatorics/Progressions/Linear/AllocatedKernelScaleWithCutoff.lean`); the definitions it uses are in the definitions bundle `OAIE3v2B176` of version 2 of this split (and the bundles they import).
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/Progressions/Linear/AllocatedKernelScaleWithCutoff.lean (declaration OAI.Erdos3.VectorPolynomial.allocatedContinuousKernelDensity_bounds)

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIE3v2B176

section

namespace OAI

section

namespace Erdos3

open MeasureTheory
open scoped NNReal BigOperators Matrix Classical

namespace VectorPolynomial

variable {m : ℕ} {G : Type*} [Fintype G] {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U basis R σ)
variable (j : Fin m) (i : I j)

local notation "unitWidth" => allocatedUnitProfileWidth (R j) (σ j)
  (Fintype.card (BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val+1)))

local notation "centers" => allocatedContinuousProfileCenters (G := G) B R j i
local notation "widths" => allocatedContinuousProfileWidths (G := G) B R σ j i
local notation "reindex" => allocatedKernelCoefficientEquiv (G := G) B j
local notation "grid" => allocatedGridAxis (I := I) U basis (LayerSamplerScale.value S)
local notation "sides" => allocatedPrincipalSides B U basis S

variable {α O : Type*} [Fintype α] [DecidableEq α] [Fintype O] [DecidableEq O]
variable (x : G → IntegerScalarCubeBox α S.value)
variable (u : PrincipalAxisTuples (α := α) (allocatedGridAxis (I := I) U basis S.value)
  (allocatedPrincipalSides B U basis S))
variable (rows : O → Finset α) (s : O ↪ BoundedIntegerExponent G (j.val+1))
variable (hA : ((scalarKernelIntegerJet x (j.val+1) rows).submatrix id s).det ≠ 0)

local notation "input" => partitionedPrincipalInput grid (fun g a => (g, a))
local notation "fixedReal" => Sum.elim
  (fun ga : G × Option α => ((x (Prod.fst ga) (Prod.snd ga) : ℤ) : ℝ) / (S.value : ℝ))
  (principalTupleNormalized (principalAxisLength grid sides) u)
local notation "kernelScale" => kernelJetCoefficientScale G (j.val+1) (S.value : ℝ) 1
local notation "pivot" => normalizedPivotEquiv (Matrix.submatrix (scalarKernelIntegerJet x (j.val+1) rows) id s) hA
  (fun o => kernelScale (s o)) (fun _ => 1)
  (fun o => kernelJetCoefficientScale_pos G (j.val+1)
    (Nat.cast_pos.mpr (LayerSamplerScale.positive S)) zero_lt_one (s o))
  (fun _ => zero_lt_one)
local notation "free" => matrixSupCLM (normalizedIntegerColumns
  (remainingMatrixColumns (scalarKernelIntegerJet x (j.val+1) rows) s)
  (fun d => kernelScale (Subtype.val d)) (fun _ => 1))
local notation "radius" => NNReal.mk (R j) (le_of_lt (hR j))
local notation "delta" => NNReal.mk unitWidth (le_of_lt (allocatedUnitProfileWidth_pos (hR j) (hσ j) _))

include hR hσ in
theorem allocatedContinuousKernelDensity_bounds_s2 (hσ1 : σ j ≤ 1) (v : O → ℝ) :
    (∀ y, |allocatedContinuousKernelDensity B U basis S j i x u rows s hA y v| ≤
      pivotKernelCap (UnselectedColumn s) pivot radius
        (delta⁻¹^Fintype.card (BoundedIntegerExponent G (j.val+1)))) ∧
      LipschitzOnWith
        (pivotKernelLip (UnselectedColumn s) pivot radius
          (affineProductProfileLip (BoundedIntegerExponent G (j.val+1)) delta) *
          (Fintype.card (AllocatedNonkernelCoefficient (G := G) B j) *
            polynomialBoxLip
              (Fintype.card (PrincipalAxisParameter (B := B) (h := layerSamplerDegree I n)
                (α := α) (fun a => ¬grid a))) (j.val+1) (normalizedJetMass α (j.val+1))) * radius)
        (fun y => allocatedContinuousKernelDensity B U basis S j i x u rows s hA y v)
        (Metric.closedBall 0 1) := by
  sorry

end VectorPolynomial
end Erdos3

end

end OAI
end
