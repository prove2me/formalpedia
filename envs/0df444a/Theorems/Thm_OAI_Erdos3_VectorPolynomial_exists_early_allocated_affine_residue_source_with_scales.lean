-- Prove2me | Theorems.Thm_OAI_Erdos3_VectorPolynomial_exists_early_allocated_affine_residue_source_with_scales
-- name    : OAI.Erdos3.VectorPolynomial.exists_early_allocated_affine_residue_source_with_scales
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-10-10T00:18:48.721019+00:00
-- url     : https://prove2.me/theorems/966737e5-cca0-4cf2-9ae4-3b3d4ff546c8
-- title:
--   Source radii and a tolerance make residue-class progression averages L1-close to the ideal
-- statement:
--   Fix $m \in \mathbb N$, a finite type $G$ with decidable equality, finite types $I_j$ ($j \in \mathrm{Fin}\,m$), $n : \mathrm{Fin}\,m \to \mathbb N$, finite types $B_a$ with decidable equality indexed by $a \in$ `LayerSamplerAxis I n` (the sigma type $\Sigma_j\, I_j \oplus \mathrm{Fin}(n_j)$), a finite type $\alpha$ with decidable equality, nonempty finite types $O_j$ with decidable equality, and maps $\mathrm{rows}_j : O_j \to \mathrm{Finset}\,\alpha$ that are injective with $|\mathrm{rows}_j(o)| \le j+1$ for all $j, o$. Let $\psi : \mathbb R \to \mathbb R$ be $C^\infty$ with values in $[0,1]$, $\psi(t) = 0$ for $|t| \le 1$ and $\psi(t) = 1$ for $|t| \ge 2$; let $A, T \ge 0$ be such that $\psi$ is $A$-Lipschitz and Mathlib's `Real.smoothTransition` is $T$-Lipschitz; let $\mathrm{block}_a : O_{a.1} \to B_a$ be injective for every $a$; and let $\delta, \eta$ be reals with $0 < \delta \le 1$ and $0 < \eta$. Then there exist a nonnegative real $\rho_{\min} > 0$ and a function $\rho$ from predicates on `LayerSamplerAxis I n` to nonnegative reals such that, for every predicate $P$, $\rho_{\min} \le \rho(P) \le 1$ and $\rho(P) =$ `partitionedAffineSourceRadius` (with block types $B$, output types $a \mapsto O_{a.1}$ on $\{a \mid \neg P\,a\}$, $\alpha$, degrees `layerSamplerDegree I n`, $P$, $A$, $T$, $\delta/2$, $\eta$), and a real $t$ with $0 < t \le 1$ and $t =$ `allocatedAffineSourceTolerance B A T (δ/2) η` (with $G$, $O$, $\alpha$), such that the following holds. Take any finite types $J_j$, subspaces $U_j \le \mathbb R^{J_j}$, bases $\mathrm{basis}_j$ (indexed by $\mathrm{Fin}(n_j)$) of the orthogonal complement of `euclideanSubspace (U j)`, reals $R_j > 0$ and $\sigma_j > 0$, and a `LayerSamplerScale` $S$ for $(B, U, \mathrm{basis}, R, \sigma)$ (a structure bundling a positive natural number $S.\mathrm{value}$ with width and gap inequalities) with $\sigma_j \le t$ for all $j$; write grid for `allocatedGridAxis U basis S.value` (a predicate on `LayerSamplerAxis I n`), Tuple for `PrincipalTupleIndex` over $\{a \mid \neg\,\mathrm{grid}\,a\}$ (the type $\Sigma_a\, B_a \times \mathrm{Fin}(a.1+1)$), and Jet for $\Sigma_{a : \{a \mid \neg\,\mathrm{grid}\,a\}} O_{a.1}$. Take any $x : G \to$ `IntegerScalarCubeBox α S.value` (integer vectors indexed by $\mathrm{Option}\,\alpha$ with entries in $[-S.\mathrm{value}, S.\mathrm{value})$), $u \in$ `PrincipalAxisTuples grid (allocatedPrincipalSides B U basis S)`, embeddings $s_j : O_j \hookrightarrow$ `BoundedIntegerExponent G (j+1)` such that the square submatrix of the integer matrix `scalarKernelIntegerJet x (j+1) (rows j)` on the columns $s_j$ has nonzero determinant ($h_A$), $M_k \in \mathbb N$ with $M_k > 0$ and `fixedKernelInverseBound S.positive x (j+1) (rows j) (s j) (hA j) (1/M_k)` for all $j$, and a real $P \ge 0$ with $M_k \le \exp P$ and, for all $j$, $R_j \le \exp P$, $R_j^{-1} \le \exp P$, $\sigma_j^{-1} \le \exp P$ and $|$`BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j+1)`$| + 1 \le \exp P$. Take any $L, \mathrm{step}, H, M : \mathrm{Tuple} \to \mathbb N$ and $c : \mathrm{Tuple} \to \mathbb Z$ with, for all $j$: $L_j > 0$, $\mathrm{step}_j > 0$, $H_j \ge 2$, the progression `integerProgressionSupport (c j) (step j) (H j)` (the set $\{c_j + \mathrm{step}_j\,k : 0 \le k < H_j\}$) contained in $[0, L_j)$, and $\delta L_j \le$ its cardinality; any $\mathrm{modulus} : \mathrm{Tuple} \to \mathrm{Option}\,\alpha \to \mathbb N$ and residues $\mathrm{residue}_{j,i} \in \mathbb Z/\mathrm{modulus}_{j,i}$ with $0 < \mathrm{modulus}_{j,i} \le M_j$, $(|\alpha|+1)M_j \le H_j$, and $\kappa\,(M_j/H_j) < \mathrm{vol}($`scalarCubeDomain α`$)$ for all $j, i$, where $\kappa =$ `scalarCubeGridBoundaryConstant α` $= |\mathrm{Bool} \times \mathrm{Finset}\,\alpha| \cdot 4^{|\alpha|} \cdot 2(|\alpha|+1)$ and `scalarCubeDomain α` is a subset of $\mathbb R^{\mathrm{Option}\,\alpha}$; and any real $\varepsilon \ge 0$ with $\mathrm{step}_j / L_j \le \varepsilon$ for all $j$. Put center $=$ `principalProgressionSliceCenter L c` and width $=$ `principalProgressionSliceWidth L H step` (real functions on `PrincipalAxisParameter (¬grid)`); let $\mathrm{ideal} =$ `diagonalImageDensity (o ↦ R o.1.1.1) Φ`, where `diagonalImageDensity d f v` $= (\prod_o |d_o|)^{-1} f(v/d)$ and $\Phi =$ `activeAveragedSlicedProfileIdeal (G × Option α) (layerSamplerDegree I n) grid (a ↦ rows a.1) (ρ grid) center width`; and for $z \in \mathbb R^{\mathrm{Jet}}$ let $\mathrm{discrete}(z)$ be the mean, under the product over $j \in \mathrm{Tuple}$ of the probability weights `scalarCubeResidueWeights α (H j) (M j) _ (modulus j) (residue j) …` on `IntegerScalarCubeBox α (H j)` (OpenAI's cube weights conditioned on the residue set), of $v \mapsto$ `allocatedNormalizedLongJetDensity B U basis S x u rows s hA y_v z`, where $y_v$ is `principalTupleFlatten` applied to $(j, i) \mapsto \bigl([i = \mathrm{none}]\,c_j + \mathrm{step}_j\,v_{j,i}\bigr)/L_j$. Let $\beta = \exp($`allocatedDensityLog B α O P`$)$, $\mathrm{cap} = \beta^{N}$ and $\mathrm{lip} = N\beta\,\mathrm{cap}$ with $N = |$`LayerSamplerAxis I n`$|$. Then, with Lebesgue measure,
--   $$\int |\mathrm{ideal}(z) - \mathrm{discrete}(z)|\,dz \le \eta + \Bigl(\bigl(2\,\mathrm{cap}\,\kappa/\mathrm{vol}(\texttt{scalarCubeDomain}\ \alpha) + 2\,\mathrm{lip}\bigr)\textstyle\sum_j M_j/H_j + \mathrm{lip}\,\varepsilon\Bigr)\bigl(2\exp(\texttt{allocatedJetSupportLog}\ B\ \alpha\ O\ P)\bigr)^{|\mathrm{Jet}|}.$$
--
--   Lean: `OAI.Erdos3.VectorPolynomial.exists_early_allocated_affine_residue_source_with_scales` in `lean/OAI/Combinatorics/Progressions/Lattices/EarlyAllocatedAffineResidueSource.lean` (OpenAI); the definitions it uses are in the definitions bundles `OAIErdos3B136` of this split (and the bundles they import).
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/Progressions/Lattices/EarlyAllocatedAffineResidueSource.lean#L408

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

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open MeasureTheory
open scoped BigOperators Matrix NNReal Classical

variable {m : ℕ} {G : Type*} [Fintype G] [dG : DecidableEq G]
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
local notation "radius" => Real.exp (allocatedJetSupportLog (G := G) B α O P)
local notation "input" => PrincipalAxisParameter (B := B) (h := layerSamplerDegree I n)
  (α := α) (fun a => ¬grid a)
local notation "output" => (Σ a : {a // ¬grid a}, O (Sigma.fst (Subtype.val a)))

include hR hσ hM hi hP hMP hRP hRi hσi hcount

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

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open MeasureTheory
open scoped BigOperators ContDiff NNReal Classical

variable {m : ℕ} {G : Type*} [Fintype G] [DecidableEq G] {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)] [∀ a, DecidableEq (B a)]
variable {α : Type*} [Fintype α] [DecidableEq α]
variable {O : Fin m → Type*} [∀ j, Fintype (O j)] [∀ j, Nonempty (O j)] [∀ j, DecidableEq (O j)]
variable (rows : ∀ j, O j → Finset α)
variable (hrows : ∀ j, Function.Injective (rows j)) (hcard : ∀ j o, (rows j o).card ≤ j.val + 1)

include hrows hcard in
theorem exists_early_allocated_affine_residue_source_with_scales
    (ψ : ℝ → ℝ) (hψ : ContDiff ℝ ∞ ψ) (hrange : ∀ t, ψ t ∈ Set.Icc (0 : ℝ) 1)
    (hzero : ∀ t, |t| ≤ 1 → ψ t = 0) (hone : ∀ t, 2 ≤ |t| → ψ t = 1)
    (A T : ℝ≥0) (hLip : LipschitzWith A ψ) (hTransition : LipschitzWith T Real.smoothTransition)
    (block : ∀ a : LayerSamplerAxis I n, O a.1 → B a)
    (hblock : ∀ a, Function.Injective (block a))
    {δ η : ℝ} (hδ : 0 < δ) (hδone : δ ≤ 1) (hη : 0 < η) :
    ∃ ρmin : ℝ≥0, 0 < ρmin ∧ ∃ ρ : (LayerSamplerAxis I n → Prop) → ℝ≥0,
      (∀ P, ρmin ≤ ρ P ∧ ρ P ≤ 1) ∧
      (∀ P, (ρ P : ℝ) = partitionedAffineSourceRadius (B := B)
        (O := fun a : {a // ¬P a} => O a.val.1) (α := α) (layerSamplerDegree I n) P A T (δ / 2) η) ∧
      ∃ t : ℝ, 0 < t ∧ t ≤ 1 ∧
      t = allocatedAffineSourceTolerance (G := G) (O := O) (α := α) B A T (δ / 2) η ∧
      ∀ {J : Fin m → Type*} [∀ j, Fintype (J j)]
        (U : ∀ j, Submodule ℝ (J j → ℝ))
        (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
        {R σ : Fin m → ℝ} (_hR : ∀ j, 0 < R j) (_hσ : ∀ j, 0 < σ j)
        (S : LayerSamplerScale (G := G) B U basis R σ),
      (∀ j, σ j ≤ t) →
      ∀ (x : G → IntegerScalarCubeBox α S.value)
        (u : PrincipalAxisTuples (α := α) (allocatedGridAxis (I := I) U basis S.value) (allocatedPrincipalSides B U basis S)),
      ∀ (s : ∀ j, O j ↪ BoundedIntegerExponent G (j.val + 1))
        (hA : ∀ j, ((scalarKernelIntegerJet x (j.val + 1) (rows j)).submatrix id (s j)).det ≠ 0),
      ∀ {Mk : ℕ} (_ : 0 < Mk)
        (_ : ∀ j : Fin m, fixedKernelInverseBound S.positive x (j.val + 1) (rows j)
          (s j) (hA j) (1 / (Mk : ℝ)))
        {P : ℝ} (_ : 0 ≤ P) (_ : (Mk : ℝ) ≤ Real.exp P)
        (_ : ∀ j, R j ≤ Real.exp P) (_ : ∀ j, (R j)⁻¹ ≤ Real.exp P)
        (_ : ∀ j, (σ j)⁻¹ ≤ Real.exp P)
        (_ : ∀ j : Fin m, (Fintype.card
          (BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1)) : ℝ) + 1 ≤ Real.exp P),
      ∀ (L step H M : (PrincipalTupleIndex (fun a : {a // ¬(allocatedGridAxis (I := I) U basis S.value) a} => B a.val) (fun a : {a // ¬(allocatedGridAxis (I := I) U basis S.value) a} => layerSamplerDegree I n a.val)) → ℕ) (c : (PrincipalTupleIndex (fun a : {a // ¬(allocatedGridAxis (I := I) U basis S.value) a} => B a.val) (fun a : {a // ¬(allocatedGridAxis (I := I) U basis S.value) a} => layerSamplerDegree I n a.val)) → ℤ)
        (_ : ∀ j, 0 < L j) (_ : ∀ j, 0 < step j) (hH : ∀ j, 2 ≤ H j)
        (_ : ∀ j, integerProgressionSupport (c j) (step j : ℤ) (H j) ⊆ Finset.Ico (0 : ℤ) (L j : ℤ))
        (_ : ∀ j, δ * L j ≤ ((integerProgressionSupport (c j) (step j : ℤ) (H j)).card : ℝ))
        (modulus : (PrincipalTupleIndex (fun a : {a // ¬(allocatedGridAxis (I := I) U basis S.value) a} => B a.val) (fun a : {a // ¬(allocatedGridAxis (I := I) U basis S.value) a} => layerSamplerDegree I n a.val)) → Option α → ℕ) (residue : ∀ j i, ZMod (modulus j i))
        (hm : ∀ j i, 0 < modulus j i) (hmM : ∀ j i, modulus j i ≤ M j)
        (hsize : ∀ j, (Fintype.card α + 1) * M j ≤ H j)
        (_ : ∀ j, scalarCubeGridBoundaryConstant α * ((M j : ℝ) / H j) < volume.real (scalarCubeDomain α))
        {ε : ℝ} (_ : 0 ≤ ε) (_ : ∀ j, (step j : ℝ) / L j ≤ ε),
      let center := principalProgressionSliceCenter (α := α) (fun a : {a // ¬(allocatedGridAxis (I := I) U basis S.value) a} => B a.val) (fun a : {a // ¬(allocatedGridAxis (I := I) U basis S.value) a} => layerSamplerDegree I n a.val) L c
      let width := principalProgressionSliceWidth (α := α) (fun a : {a // ¬(allocatedGridAxis (I := I) U basis S.value) a} => B a.val) (fun a : {a // ¬(allocatedGridAxis (I := I) U basis S.value) a} => layerSamplerDegree I n a.val) L H step
      let ideal := diagonalImageDensity (fun o : (Σ a : {a // ¬(allocatedGridAxis (I := I) U basis S.value) a}, O a.val.1) => R o.1.val.1)
        (activeAveragedSlicedProfileIdeal (G := G) (B := B) (G × Option α)
          (layerSamplerDegree I n) (allocatedGridAxis (I := I) U basis S.value) (fun a => rows a.val.1) (ρ (allocatedGridAxis (I := I) U basis S.value)) center width)
      let discrete := fun z : (Σ a : {a // ¬(allocatedGridAxis (I := I) U basis S.value) a}, O a.val.1) → ℝ =>
        (FiniteProbabilityWeights.pi (fun j => scalarCubeResidueWeights α (H j) (M j)
          (by have := hH j; omega) (modulus j) (residue j) (hm j) (hmM j) (hsize j))).mean
          (fun v => allocatedNormalizedLongJetDensity B U basis S x u rows s hA
            (principalTupleFlatten (fun a : {a // ¬(allocatedGridAxis (I := I) U basis S.value) a} => B a.val) (fun a : {a // ¬(allocatedGridAxis (I := I) U basis S.value) a} => layerSamplerDegree I n a.val) α
              (fun j i => ((if i = none then (c j : ℝ) else 0) + (step j : ℝ) * (v j i : ℝ)) / L j)) z)
      let bound : ℝ≥0 := ⟨Real.exp (allocatedDensityLog (G := G) B α O P), Real.exp_nonneg _⟩
      let cap := bound ^ Fintype.card (LayerSamplerAxis I n)
      let lip := (Fintype.card (LayerSamplerAxis I n) : ℝ≥0) * bound * cap
      (∫ z, |ideal z - discrete z|) ≤ η +
        ((2 * (cap : ℝ) * scalarCubeGridBoundaryConstant α / volume.real (scalarCubeDomain α) +
          (lip : ℝ) * 2) * ∑ j, (M j : ℝ) / H j + (lip : ℝ) * ε) *
          (2 * Real.exp (allocatedJetSupportLog (G := G) B α O P)) ^ Fintype.card (Σ a : {a // ¬(allocatedGridAxis (I := I) U basis S.value) a}, O a.val.1) := by
  sorry

end Erdos3.VectorPolynomial
end
end OAI
