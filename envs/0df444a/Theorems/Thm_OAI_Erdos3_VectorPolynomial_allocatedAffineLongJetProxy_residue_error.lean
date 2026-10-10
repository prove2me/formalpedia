-- Prove2me | Theorems.Thm_OAI_Erdos3_VectorPolynomial_allocatedAffineLongJetProxy_residue_error
-- name    : OAI.Erdos3.VectorPolynomial.allocatedAffineLongJetProxy_residue_error
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-10-10T00:35:43.035795+00:00
-- url     : https://prove2.me/theorems/04b12c98-9df5-4e49-b73b-9f28d97c47e5
-- title:
--   Residue-conditioned averages of the long-jet density approximate the affine proxy
-- statement:
--   Fix the section data: a natural number $m$; a finite type $G$ with decidable equality; finite types $I_j$, natural numbers $n_j$, finite types $B_a$ with decidable equality over the axes $a$ of `LayerSamplerAxis I n`; finite types $J_j$, real subspaces $U_j \subseteq \mathbb R^{J_j}$ and bases `basis j` (indexed by $\mathrm{Fin}\,n_j$) of the orthogonal complements of `euclideanSubspace (U j)`; real functions $R, \sigma$ on $\mathrm{Fin}\,m$ with $R_j > 0$ and $\sigma_j > 0$; a layer-sampler scale `S : LayerSamplerScale B U basis R σ`; a finite type $\alpha$ with decidable equality and a point $x : G \to $ `IntegerScalarCubeBox α S.value`; a grid tuple $u$ in `PrincipalAxisTuples (allocatedGridAxis U basis S.value) (allocatedPrincipalSides B U basis S)`; finite types $O_j$ with decidable equality and maps $\mathrm{rows}_j : O_j \to \mathrm{Finset}\,\alpha$; embeddings $s_j : O_j \hookrightarrow$ `BoundedIntegerExponent G (j+1)` with the column-restricted matrices of `scalarKernelIntegerJet x (j+1) (rows j)` nonsingular ($hA$); a positive natural number $M_k$ with `fixedKernelInverseBound S.positive x (j+1) (rows j) (s j) (hA j) (1/Mk)` for all $j$; and a real $P \ge 0$ with $M_k \le e^P$, $R_j \le e^P$, $R_j^{-1} \le e^P$, $\sigma_j^{-1} \le e^P$ and $|\texttt{BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j+1)}| + 1 \le e^P$ for all $j$. Let grid be the predicate `allocatedGridAxis U basis S.value`, Tuple the principal tuple index over the non-grid axes, Jet $= \Sigma_{a\ \text{non-grid}}\, O_{\mathrm{layer}(a)}$, $\beta = \exp(\texttt{allocatedDensityLog B α O P})$, $\mathrm{cap} = \beta^{N}$ and $\mathrm{lip} = N\beta\,\mathrm{cap}$, where $N$ is the number of axes.
--
--   Assume $\sigma_j \le 1$ for all $j$. Let $L, \mathrm{step}, H, M : \mathrm{Tuple} \to \mathbb N$ and $c : \mathrm{Tuple} \to \mathbb Z$ with $L_j > 0$, $\mathrm{step}_j > 0$, $H_j \ge 2$; let $\delta > 0$ with each progression $\{c_j + \mathrm{step}_j k : 0 \le k < H_j\}$ contained in $[0, L_j)$ and of cardinality at least $\delta L_j$; let $\mathrm{modulus}_j(i)$ and $\mathrm{residue}_j(i) \in \mathbb Z/\mathrm{modulus}_j(i)$ for $i \in \mathrm{Option}\,\alpha$, with $0 < \mathrm{modulus}_j(i) \le M_j$; assume $(|\alpha|+1)M_j \le H_j$ and $K_\alpha M_j/H_j < V_\alpha$, where $K_\alpha = $ `scalarCubeGridBoundaryConstant α` and $V_\alpha$ is the Lebesgue measure of `scalarCubeDomain α`; let $\varepsilon \ge 0$ with $\mathrm{step}_j/L_j \le \varepsilon$; and let $z : \mathrm{Jet} \to \mathbb R$. Let $\mu$ be the product over $j$ of the weights `scalarCubeResidueWeights α (H j) (M j) … (modulus j) (residue j) …` (uniform weights on the integer scalar cube conditioned on the residues). Then
--   $$\Bigl| \sum_v \mu(v)\,\texttt{allocatedNormalizedLongJetDensity B U basis S x u rows s hA}\ (\pi(v))\ z - \texttt{allocatedAffineLongJetProxy B U basis S x u rows s hA}\ \mathrm{center}\ \mathrm{width}\ z \Bigr| \le \Bigl(\frac{2\,\mathrm{cap}\,K_\alpha}{V_\alpha} + 2\,\mathrm{lip}\Bigr)\sum_j \frac{M_j}{H_j} + \mathrm{lip}\cdot\varepsilon,$$
--   where $\pi(v)$ is the flattening (`principalTupleFlatten`) of $(j, i) \mapsto ([i = \mathrm{none}]\,c_j + \mathrm{step}_j\, v_j(i))/L_j$, and center, width are `principalProgressionSliceCenter … L c` (the flattening of $c_j/L_j$ at $i = \mathrm{none}$ and $0$ elsewhere) and `principalProgressionSliceWidth … L H step` (the flattening of $\mathrm{step}_j(H_j - 1)/L_j$).
--
--   Lean: `OAI.Erdos3.VectorPolynomial.allocatedAffineLongJetProxy_residue_error` in `lean/OAI/Combinatorics/Progressions/Lattices/EarlyAllocatedAffineResidueSource.lean` (OpenAI); the definitions it uses are in the definitions bundles `OAIErdos3B136` of this split (and the bundles they import).
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/Progressions/Lattices/EarlyAllocatedAffineResidueSource.lean#L151

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIErdos3B136

namespace OAI

section

namespace Erdos3.VectorPolynomial
open MeasureTheory
open scoped ContDiff NNReal Classical

variable {m : ℕ} {G : Type*} [Fintype G] {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {α : Type*} [Fintype α] [DecidableEq α]
variable {O : Fin m → Type*} [∀ j, Fintype (O j)] [∀ j, Nonempty (O j)] [∀ j, DecidableEq (O j)]
variable (rows : ∀ j, O j → Finset α)
variable (hrows : ∀ j, Function.Injective (rows j)) (hcard : ∀ j o, (rows j o).card ≤ j.val + 1)

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open MeasureTheory
open scoped Classical BigOperators NNReal

variable {m : ℕ} {G : Type*} [Fintype G] [DecidableEq G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*)
variable [∀ a, Fintype (B a)] [∀ a, DecidableEq (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U basis R σ)
variable {α : Type*} [Fintype α] [DecidableEq α]
variable (x : G → IntegerScalarCubeBox α S.value)
variable (u : PrincipalAxisTuples (α := α) (allocatedGridAxis (I := I) U basis S.value)
  (allocatedPrincipalSides B U basis S))
variable {O : Fin m → Type*} [∀ j, Fintype (O j)] [∀ j, DecidableEq (O j)]
variable (rows : ∀ j, O j → Finset α)
variable (s : ∀ j : Fin m, O j ↪ BoundedIntegerExponent G (j.val + 1))
variable (hA : ∀ j, ((scalarKernelIntegerJet x (j.val + 1) (rows j)).submatrix id (s j)).det ≠ 0)
variable {Mk : ℕ} (hMk : 0 < Mk)
variable (hi : ∀ j : Fin m, fixedKernelInverseBound (O := O j)
  S.positive x (j.val + 1) (rows j) (s j) (hA j) (1 / (Mk : ℝ)))
variable {P : ℝ} (hP : 0 ≤ P) (hMkP : (Mk : ℝ) ≤ Real.exp P)
variable (hRP : ∀ j, R j ≤ Real.exp P) (hRi : ∀ j, (R j)⁻¹ ≤ Real.exp P)
variable (hσi : ∀ j, (σ j)⁻¹ ≤ Real.exp P)
variable (hcount : ∀ j : Fin m, (Fintype.card
  (BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1)) : ℝ) + 1 ≤ Real.exp P)

local notation "grid" => allocatedGridAxis (I := I) U basis S.value
local notation "degree" => layerSamplerDegree I n
local notation "Tuple" => PrincipalTupleIndex (fun a : {a // ¬grid a} => B (Subtype.val a)) (fun a => degree (Subtype.val a))
local notation "Jet" => (Σ a : {a // ¬grid a}, O (Sigma.fst (Subtype.val a)))
local notation "bound" => NNReal.mk
  (Real.exp (allocatedDensityLog (G := G) B α O P)) (Real.exp_nonneg _)
local notation "cap" => bound ^ Fintype.card (LayerSamplerAxis I n)
local notation "lip" => (Fintype.card (LayerSamplerAxis I n) : ℝ≥0) * bound * cap

include hR hσ hMk hi hP hMkP hRP hRi hσi hcount in
theorem allocatedAffineLongJetProxy_residue_error (hσ1 : ∀ j, σ j ≤ 1)
    (L step H M : Tuple → ℕ) (c : Tuple → ℤ)
    (hL : ∀ j, 0 < L j) (hstep : ∀ j, 0 < step j) (hH : ∀ j, 2 ≤ H j)
    {δ : ℝ} (hδ : 0 < δ)
    (hsubset : ∀ j, integerProgressionSupport (c j) (step j : ℤ) (H j) ⊆ Finset.Ico (0 : ℤ) (L j : ℤ))
    (hdense : ∀ j, δ * L j ≤ ((integerProgressionSupport (c j) (step j : ℤ) (H j)).card : ℝ))
    (modulus : Tuple → Option α → ℕ) (residue : ∀ j i, ZMod (modulus j i))
    (hm : ∀ j i, 0 < modulus j i) (hmM : ∀ j i, modulus j i ≤ M j)
    (hsize : ∀ j, (Fintype.card α + 1) * M j ≤ H j)
    (hsmall : ∀ j, scalarCubeGridBoundaryConstant α * ((M j : ℝ) / H j) <
      volume.real (scalarCubeDomain α))
    {ε : ℝ} (hε : 0 ≤ ε) (hmesh : ∀ j, (step j : ℝ) / L j ≤ ε) (z : Jet → ℝ) :
    |(FiniteProbabilityWeights.pi (fun j => scalarCubeResidueWeights α (H j) (M j)
        (by have := hH j; omega) (modulus j) (residue j) (hm j) (hmM j) (hsize j))).mean
        (fun v => allocatedNormalizedLongJetDensity B U basis S x u rows s hA
          (principalTupleFlatten (fun a : {a // ¬grid a} => B a.val) (fun a => degree a.val) α
            (fun j i => ((if i = none then (c j : ℝ) else 0) + (step j : ℝ) * (v j i : ℝ)) / L j)) z) -
      allocatedAffineLongJetProxy B U basis S x u rows s hA
        (principalProgressionSliceCenter (α := α) (fun a : {a // ¬grid a} => B a.val)
          (fun a => degree a.val) L c)
        (principalProgressionSliceWidth (α := α) (fun a : {a // ¬grid a} => B a.val)
          (fun a => degree a.val) L H step) z| ≤
      (2 * (cap : ℝ) * scalarCubeGridBoundaryConstant α / volume.real (scalarCubeDomain α) +
        (lip : ℝ) * 2) * ∑ j, (M j : ℝ) / H j + (lip : ℝ) * ε := by
  sorry

end Erdos3.VectorPolynomial
end
end OAI
