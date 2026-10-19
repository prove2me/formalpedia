-- Prove2me | Theorems.Thm_OAI_Erdos3_VectorPolynomial_allocatedIntegerKernelDensity_bounds_s2
-- name    : OAI.Erdos3.VectorPolynomial.allocatedIntegerKernelDensity_bounds_s2
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-17T11:04:10.418511+00:00
-- url     : https://prove2.me/theorems/4da91655-f210-4e01-a257-e09c78c1e34f
-- title:
--   Uniform and Lipschitz bounds for the allocated integer kernel density in the non-grid parameters
-- statement:
--   Let $m$ be a natural number and $G$ a finite type. For each $j < m$ let $I_j$ and $J_j$ be finite types, $n_j$ a natural number, $U_j$ a real subspace of $\mathbb{R}^{J_j}$ and $\mathrm{basis}_j$ a real basis, indexed by $\{0, \dots, n_j - 1\}$, of the orthogonal complement of the Euclidean subspace given by $U_j$. For each layer sampler axis $a$ (OpenAI's `LayerSamplerAxis I n`: pairs $(j, c)$ with $c \in I_j \sqcup \{0, \dots, n_j - 1\}$) let $B_a$ be a finite type. Let $R, \sigma : \{0,\dots,m-1\} \to \mathbb{R}$ with $R_j > 0$ and $\sigma_j > 0$ for all $j$, and let $S$ be a layer sampler scale (OpenAI's `LayerSamplerScale B U basis R σ`, with main field a positive natural number `S.value`). Fix $j < m$ and $i < n_j$, and assume $\sigma_j \le 1$.
--
--   Let $\alpha, O$ be finite types with decidable equality, $x : G \to$ `IntegerScalarCubeBox α S.value` (each $x_g$ maps $\mathrm{Option}\,\alpha$ to the integers in $[-\texttt{S.value}, \texttt{S.value})$), and $u$ a principal axis tuple for the grid axes `allocatedGridAxis U basis S.value` with the sides `allocatedPrincipalSides B U basis S` (OpenAI objects; see the related statement on the continuous kernel image law). Let $\mathrm{rows} : O \to \mathrm{Finset}\,\alpha$ and $s$ an embedding of $O$ into the exponent vectors on $G$ of total degree at most $j+1$, and assume that the square submatrix $A_s$, with columns selected by $s$, of the integer matrix `scalarKernelIntegerJet x (j+1) rows` (OpenAI) has nonzero determinant. Let $h$ = `basisAxisScale (basis j) i` $= \lceil 1/\lVert \mathrm{basis}_j(i) \rVert \rceil$, and for an exponent vector $e$ on $G$ let $\kappa(e)$ = `kernelJetCoefficientScale G (j+1) S.value h e` $= h / \texttt{S.value}^{|e|}$, where $|e|$ is the total degree. Let $\Pi$ = `normalizedPivotEquiv A_s …`, the invertible linear map of $\mathbb{R}^{O}$ given by the matrix $h^{-1} A_s \operatorname{diag}(\kappa(s(o)))_o$ (OpenAI). Let $\delta$ = `allocatedUnitProfileWidth R_j σ_j N_j` (an explicit positive real defined by OpenAI), where $N_j$ is the number of exponent vectors of total degree at most $j+1$ in the layer sampler variables, and let $K$ be the number of exponent vectors on $G$ of total degree at most $j+1$.
--
--   Let $z \in \mathbb{R}^{O}$. For $y$ a real assignment to the non-grid principal parameters (OpenAI's `PrincipalAxisParameter … (fun a => ¬grid a)`), write $\rho(y)$ = `allocatedIntegerKernelDensity B U basis S j i x u rows s hA y z`, an explicit density defined by OpenAI (an affine selected-jet density built from $\Pi$, the remaining normalized columns, the real normalized data of $x$ and $u$, and OpenAI's allocated integer profile centers and widths at $(j, i)$). Then:
--   1. for every $y$, $|\rho(y)| \le$ `pivotKernelCap (UnselectedColumn s) Π R_j (δ^{-1})^K`, where `pivotKernelCap J Π R H` $= |\det \Pi^{-1}| \cdot H \cdot (2R)^{|J|}$ (OpenAI) and `UnselectedColumn s` is the set of exponent vectors not in the range of $s$;
--   2. $y \mapsto \rho(y)$ is Lipschitz on the closed unit ball of the parameter space (sup norm) with constant
--   $$\texttt{pivotKernelLip}\ (\texttt{UnselectedColumn}\ s)\ \Pi\ R_j\ \bigl(\texttt{affineProductProfileLip}\ (\cdot)\ \delta\bigr)\cdot \Bigl(|\mathrm{NK}_j| \cdot \texttt{polynomialBoxLip}\ |\mathrm{Par}|\ (j+1)\ \bigl(\texttt{normalizedJetMass}\ \alpha\ (j+1)\bigr)\Bigr)\cdot R_j,$$
--   where `pivotKernelLip J Π R K'` $=$ `pivotKernelCap J Π R K'` $\cdot \lVert \Pi^{-1} \rVert$; `affineProductProfileLip` (applied to the exponent vectors on $G$ of total degree at most $j+1$, $K$ of them) $= K \cdot \Lambda \cdot \delta^{-(K+1)}$ with $\Lambda$ = `probabilityProfileLipschitz`, a Lipschitz constant of OpenAI's smooth probability profile; $|\mathrm{NK}_j|$ is the number of elements of OpenAI's `AllocatedNonkernelCoefficient B j`; $|\mathrm{Par}|$ is the number of non-grid principal parameters; `polynomialBoxLip n d C` $= n\,(d+1)^{n}\, d\, C$; and `normalizedJetMass α d` $= 2^{|\alpha|}(|\alpha|+1)^{d}$ (all defined by OpenAI).
--
--   Lean: `OAI.Erdos3.VectorPolynomial.allocatedIntegerKernelDensity_bounds_s2`, which states OpenAI's `OAI.Erdos3.VectorPolynomial.allocatedIntegerKernelDensity_bounds` (in `lean/OAI/Combinatorics/Progressions/Lattices/AllocatedIntegerKernelComparison.lean`); the definitions it uses are in the definitions bundle `OAIE3v2B125` of version 2 of this split (and the bundles they import).
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/Progressions/Lattices/AllocatedIntegerKernelComparison.lean (declaration OAI.Erdos3.VectorPolynomial.allocatedIntegerKernelDensity_bounds)

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIE3v2B125

section

namespace OAI

section

namespace Erdos3.VectorPolynomial

open MeasureTheory
open scoped BigOperators Matrix Classical

variable {m : ℕ} {G : Type*} [Fintype G] {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U basis R σ)
variable (j : Fin m) (i : Fin (n j))

local notation "unitWidth" => allocatedUnitProfileWidth (R j) (σ j)
  (Fintype.card (BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val+1)))

local notation "centers" => allocatedIntegerProfileCenters (G := G) B R j i
local notation "widths" => allocatedIntegerProfileWidths (G := G) B R σ j i
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
local notation "height" => (basisAxisScale (basis j) i : ℝ)
local notation "heightPos" => Nat.cast_pos.mpr (basisAxisScale_pos (basis j) i)
local notation "kernelScale" => kernelJetCoefficientScale G (j.val+1) (S.value : ℝ) height
local notation "pivot" => normalizedPivotEquiv (Matrix.submatrix (scalarKernelIntegerJet x (j.val+1) rows) id s) hA
  (fun o => kernelScale (s o)) (fun _ => height)
  (fun o => kernelJetCoefficientScale_pos G (j.val+1)
    (Nat.cast_pos.mpr (LayerSamplerScale.positive S)) heightPos (s o))
  (fun _ => heightPos)
local notation "free" => matrixSupCLM (normalizedIntegerColumns
  (remainingMatrixColumns (scalarKernelIntegerJet x (j.val+1) rows) s)
  (fun d => kernelScale (Subtype.val d)) (fun _ => height))
local notation "radius" => NNReal.mk (R j) (le_of_lt (hR j))
local notation "delta" => NNReal.mk unitWidth (le_of_lt (allocatedUnitProfileWidth_pos (hR j) (hσ j) _))

include hR hσ in
theorem allocatedIntegerKernelDensity_bounds_s2 (hσ1 : σ j ≤ 1) (z : O → ℝ) :
    (∀ y, |allocatedIntegerKernelDensity B U basis S j i x u rows s hA y z| ≤
      pivotKernelCap (UnselectedColumn s) pivot radius
        (delta⁻¹^Fintype.card (BoundedIntegerExponent G (j.val+1)))) ∧
      LipschitzOnWith
        (pivotKernelLip (UnselectedColumn s) pivot radius
          (affineProductProfileLip (BoundedIntegerExponent G (j.val+1)) delta) *
          (Fintype.card (AllocatedNonkernelCoefficient (G := G) B j) *
            polynomialBoxLip
              (Fintype.card (PrincipalAxisParameter (B := B) (h := layerSamplerDegree I n)
                (α := α) (fun a => ¬grid a))) (j.val+1) (normalizedJetMass α (j.val+1))) * radius)
        (fun y => allocatedIntegerKernelDensity B U basis S j i x u rows s hA y z)
        (Metric.closedBall 0 1) := by
  sorry

end Erdos3.VectorPolynomial

end

end OAI
end
