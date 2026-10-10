-- Prove2me | Theorems.Thm_OAI_Erdos3_VectorPolynomial_allocatedFiniteLongJetDensity_regularity
-- name    : OAI.Erdos3.VectorPolynomial.allocatedFiniteLongJetDensity_regularity
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-10-09T22:48:21.295035+00:00
-- url     : https://prove2.me/theorems/5a83fca8-7773-4ecc-b434-8a8cfb822a32
-- title:
--   Mixtures of normalized long-jet densities are bounded, Lipschitz, supported, integrable
-- statement:
--   Fix the section data: a natural number $m$; a finite type $G$ with decidable equality; finite types $I_j$, natural numbers $n_j$, finite types $B_a$ over the axes $a$ of `LayerSamplerAxis I n`; finite types $J_j$, real subspaces $U_j \subseteq \mathbb R^{J_j}$ and bases `basis j` (indexed by $\mathrm{Fin}\,n_j$) of the orthogonal complements of `euclideanSubspace (U j)`; real functions $R, \sigma$ on $\mathrm{Fin}\,m$ with $R_j > 0$ and $\sigma_j > 0$; a layer-sampler scale `S : LayerSamplerScale B U basis R σ`; a finite type $\alpha$ with decidable equality and a point $x : G \to $ `IntegerScalarCubeBox α S.value`; finite types $O_j$ with decidable equality and maps $\mathrm{rows}_j : O_j \to \mathrm{Finset}\,\alpha$; embeddings $s_j : O_j \hookrightarrow$ `BoundedIntegerExponent G (j+1)` with the column-restricted matrices of `scalarKernelIntegerJet x (j+1) (rows j)` nonsingular ($hA$); a positive natural number $M$ with `fixedKernelInverseBound S.positive x (j+1) (rows j) (s j) (hA j) (1/M)` for all $j$; a real $P \ge 0$ with $M \le e^P$, $R_j \le e^P$, $R_j^{-1} \le e^P$, $\sigma_j^{-1} \le e^P$ and $|\texttt{BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j+1)}| + 1 \le e^P$ for all $j$; and a grid tuple $u$ in `PrincipalAxisTuples (allocatedGridAxis U basis S.value) (allocatedPrincipalSides B U basis S)`. Let grid be the predicate `allocatedGridAxis U basis S.value`, input $=$ `PrincipalAxisParameter (¬ grid)`, output $= \Sigma_{a\ \text{non-grid}}\, O_{\mathrm{layer}(a)}$, $\beta = \exp(\texttt{allocatedDensityLog B α O P})$, $\mathrm{cap} = \beta^{N}$ and $\mathrm{lip} = N\beta\,\mathrm{cap}$ with $N$ the number of axes, and $r = \exp(\texttt{allocatedJetSupportLog B α O P})$.
--
--   Assume $\sigma_j \le 1$ for all $j$. Let $w$ be finite probability weights on a finite type $\Omega$ and $F : \Omega \to (\mathrm{input} \to \mathbb R)$ with $\|F(v)\| \le 1$ (sup norm) whenever $w(v) \ne 0$. Let $\rho(z) = \sum_v w(v)\,$`allocatedNormalizedLongJetDensity B U basis S x u rows s hA (F v) z` for $z : \mathrm{output} \to \mathbb R$. Then $|\rho(z)| \le \mathrm{cap}$ for all $z$; $\rho$ is $\mathrm{lip}$-Lipschitz; $\rho(z) = 0$ whenever $\|z\| > r$; and $\rho$ is Lebesgue integrable.
--
--   Lean: `OAI.Erdos3.VectorPolynomial.allocatedFiniteLongJetDensity_regularity` in `lean/OAI/Combinatorics/Progressions/Estimates/AllocatedFiniteProxyRegularity.lean` (OpenAI); the definitions it uses are in the definitions bundles `OAIErdos3B132` of this split (and the bundles they import).
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/Progressions/Estimates/AllocatedFiniteProxyRegularity.lean#L47

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIErdos3B132

namespace OAI

section

namespace Erdos3.VectorPolynomial

open MeasureTheory
open scoped BigOperators NNReal Classical

variable {m : ℕ} {G : Type*} [Fintype G] [DecidableEq G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U basis R σ)
variable {α : Type*} [Fintype α] [DecidableEq α] (x : G → IntegerScalarCubeBox α S.value)
variable {O : Fin m → Type*} [∀ j, Fintype (O j)] [∀ j, DecidableEq (O j)]
variable (rows : ∀ j, O j → Finset α)
variable (s : ∀ j, O j ↪ BoundedIntegerExponent G (j.val + 1))
variable (hA : ∀ j, ((scalarKernelIntegerJet x (j.val + 1) (rows j)).submatrix id (s j)).det ≠ 0)
variable {M : ℕ} (hM : 0 < M)
variable (hi : ∀ j : Fin m,
  fixedKernelInverseBound S.positive x (j.val + 1) (rows j) (s j) (hA j) (1 / (M : ℝ)))
variable {P : ℝ} (hP : 0 ≤ P) (hMP : (M : ℝ) ≤ Real.exp P)
variable (hRP : ∀ j, R j ≤ Real.exp P) (hRi : ∀ j, (R j)⁻¹ ≤ Real.exp P)
variable (hσi : ∀ j, (σ j)⁻¹ ≤ Real.exp P)
variable (hcount : ∀ j : Fin m, (Fintype.card
  (BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1)) : ℝ) + 1 ≤ Real.exp P)
variable (u : PrincipalAxisTuples (α := α) (allocatedGridAxis (I := I) U basis S.value)
  (allocatedPrincipalSides B U basis S))

local notation "grid" => allocatedGridAxis (I := I) U basis S.value
local notation "bound" => NNReal.mk (Real.exp (allocatedDensityLog (G := G) B α O P))
  (le_of_lt (Real.exp_pos _))
local notation "cap" => bound ^ Fintype.card (LayerSamplerAxis I n)
local notation "lip" => (Fintype.card (LayerSamplerAxis I n) : ℝ≥0) * bound * cap

local notation "input" => PrincipalAxisParameter (B := B) (h := layerSamplerDegree I n)
  (α := α) (fun a => ¬grid a)
local notation "output" => (Σ a : {a // ¬grid a}, O (Sigma.fst (Subtype.val a)))
local notation "radius" => Real.exp (allocatedJetSupportLog (G := G) B α O P)

include hR hσ hM hi hP hMP hRP hRi hσi hcount in
theorem allocatedFiniteLongJetDensity_regularity (hσ1 : ∀ j, σ j ≤ 1)
    {Ω : Type*} [Fintype Ω] (weights : FiniteProbabilityWeights Ω) (F : Ω → (input → ℝ))
    (hF : ∀ v, weights.weight v ≠ 0 → ‖F v‖ ≤ 1) :
    let density := fun z : output → ℝ => weights.mean
      (fun v => allocatedNormalizedLongJetDensity B U basis S x u rows s hA (F v) z)
    (∀ z, |density z| ≤ cap) ∧ LipschitzWith lip density ∧
      (∀ z, radius < ‖z‖ → density z = 0) ∧ Integrable density := by
  sorry

end Erdos3.VectorPolynomial
end
end OAI
