-- Prove2me | Theorems.Thm_OAI_Erdos3_VectorPolynomial_allocatedIntegerKernel_residue_family
-- name    : OAI.Erdos3.VectorPolynomial.allocatedIntegerKernel_residue_family
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-09T13:54:07.648676+00:00
-- url     : https://prove2.me/theorems/3aa68735-cf62-4410-b671-e33b64215dad
-- title:
--   Local law for the allocated integer kernel PMF over a residue-sharing family
-- statement:
--   Let $m\in\mathbb N$, $G$ a finite type, $I\colon\mathrm{Fin}\,m\to$ Type a family of finite types with decidable equality, $n\colon\mathrm{Fin}\,m\to\mathbb N$, $B$ a family of finite types with decidable equality indexed by `LayerSamplerAxis I n` $=\Sigma_j\,I_j\oplus\mathrm{Fin}\,n_j$, $J\colon\mathrm{Fin}\,m\to$ Type finite types, $U_j$ a subspace of $\mathbb R^{J_j}$, `basis` $j$ a basis indexed by $\mathrm{Fin}\,n_j$ of the orthogonal complement of `euclideanSubspace (U j)`, $R,\sigma\colon\mathrm{Fin}\,m\to\mathbb R$ with $R_j>0$ and $\sigma_j>0$ (`hR`, `hσ`), and $S$ a `LayerSamplerScale B U basis R σ` (a structure bundling a positive natural number `S.value` with width and gap conditions). Let grid be the predicate `allocatedGridAxis U basis S.value` on axes and `sides` $=$ `allocatedPrincipalSides B U basis S`. Let $\alpha$ be a finite type with decidable equality, $x\colon G\to$ `IntegerScalarCubeBox α S.value`, $u\in$ `PrincipalAxisTuples grid sides`, $O_j$ finite types with decidable equality and `rows` $j\colon O_j\to$ `Finset α`. Fix $j\in\mathrm{Fin}\,m$, $i\in\mathrm{Fin}\,n_j$ and an embedding $s\colon O_j\hookrightarrow$ `BoundedIntegerExponent G (j + 1)` such that the square submatrix $K_s$ of $K=$ `scalarKernelIntegerJet x (j + 1) (rows j)` on the columns $s$ has nonzero determinant (`hA`); assume $\sigma_j\le1$ (`hσ1`) and $\texttt{S.value}^{\texttt{layerTailDegree}\ m+1}<\mathrm{height}:=$ `basisAxisScale (basis j) i` (`henormous`). Let $\mathcal N=$ `AllocatedNonkernelCoefficient B j` (a finite index type of non-kernel coefficients), $p$ a `FiniteProbabilityWeights` on `PrincipalAxisTuples (¬grid) sides`, $q\in\mathbb N$ (`modulus`) and `residue` an $O_j\times\mathcal N$ matrix over $\mathbb Z/q$. For a non-grid tuple $v$ write $N_v=$ `allocatedNonkernelJetMatrix B U basis S x u rows j v` (an integer $O_j\times\mathcal N$ matrix). Assume: (`hperiod`) $q\,\mathbb Z^{O_j}$ (`integerScalarLattice`) is contained in the range of $K$; (`hresidue`) $N_v\bmod q=$ `residue` whenever $p(v)\ne0$; reals $C,V,M\ge0$ such that (`ctrl`) for every $v$ with $p(v)\ne0$, `CoefficientFiberControl [K | N_v] s' (kernelScale ⊔ nonkernelScale) height S.value (j + 1) C V M` holds, where $[K\,|\,N_v]$ is `Matrix.fromCols`, $s'$ is $s$ followed by the left inclusion, `kernelScale` $e=$ `kernelJetCoefficientScale G (j + 1) S.value height e` (height divided by the monomial $\texttt{S.value}^{|e|}$), `nonkernelScale` $d=\mathrm{height}/$ `monomialScale (layerSamplerBox B U basis S) (allocatedNonkernelExponent B j d)`, and this structure (a proposition) bundles that the selected minor has nonzero determinant, $\mathrm{height}/\texttt{S.value}^{j+1}\le$ every scale, the selected entries are at most $C\,\texttt{S.value}^{j+1}$ in absolute value, every normalized entry is at most $C$, the inverse of the normalized selected minor has sup operator norm at most $V$, and the index of the column-span lattice is at most $M$; reals $b,t\ge0$ and $\varepsilon>0$ with $M,V,C,R_j\le e^b$ and $w^{-1}\le e^t$, where $w=$ `allocatedUnitProfileWidth (R j) (σ j) |BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j + 1)|`; and `coefficientReplacementScale s' b t ε S.value (j + 1)` $\le\mathrm{height}$ (`hlarge`; this scale is $\exp(\texttt{coefficientLogAllowance}\ldots)\,(1+\varepsilon^{-1})\,\texttt{S.value}^{(j+1)(|O_j|+1)}$). Let $\mu(z)=$ `allocatedIntegerKernelMask B U basis S x rows j modulus residue z` $=$ `coefficientResidueMultiplier K residue z` for $z\colon O_j\to\mathbb Z$. Then $0\le\mu(z)\le M$ for every $z$; and for every $v$ with $p(v)\ne0$ and every $z\colon O_j\to\mathbb Z$,
--   $$\Big|\mathrm{height}^{|O_j|}\,\pi_v(z)-\mu(z)\cdot\texttt{allocatedIntegerKernelDensity}\ B\ U\ \mathrm{basis}\ S\ j\ i\ x\ u\ (\mathrm{rows}\ j)\ s\ \mathrm{hA}\ \big(\texttt{principalTupleNormalized}\ (\texttt{principalAxisLength}\ (\neg\mathrm{grid})\ \mathrm{sides})\ v\big)\ (z/\mathrm{height})\Big|\le\varepsilon,$$
--   where $\pi_v=$ `allocatedIntegerKernelPMF B U basis hR hσ S x u v rows j i hσ1 henormous` is the image of `allocatedEnormousProfilePMF … j i hσ1 henormous` under $a\mapsto$ `allocatedPartitionedJetMatrix B U basis S x u v rows j` $\cdot\,a$, `principalTupleNormalized L v` divides each coordinate of $v$ by its side length, and $z/\mathrm{height}$ is coordinatewise.
--
--   Lean: `OAI.Erdos3.VectorPolynomial.allocatedIntegerKernel_residue_family` in `lean/OAI/Combinatorics/Progressions/Lattices/AllocatedIntegerKernelComparison.lean` (OpenAI); the definitions it uses are in the definitions bundles `OAIErdos3B134` of this split (and the bundles they import).
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/Progressions/Lattices/AllocatedIntegerKernelComparison.lean#L310

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIErdos3B134

namespace OAI

section

namespace Erdos3.VectorPolynomial

open MeasureTheory
open scoped Matrix

variable {m : ℕ} {G : Type*} [Fintype G] {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U basis R σ)
variable {α : Type*} [DecidableEq α] (x : G → IntegerScalarCubeBox α S.value)
variable (u : PrincipalAxisTuples (α := α) (allocatedGridAxis (I := I) U basis S.value)
  (allocatedPrincipalSides B U basis S))
variable (v : PrincipalAxisTuples (α := α) (fun a => ¬allocatedGridAxis (I := I) U basis S.value a)
  (allocatedPrincipalSides B U basis S))
variable {O : Fin m → Type*} (rows : ∀ j, O j → Finset α)

local notation "grid" => allocatedGridAxis (I := I) U basis (LayerSamplerScale.value S)
local notation "input" => partitionedPrincipalInput grid (fun g a => (g, a))
local notation "fixedInteger" => Sum.elim
  (fun ga : G × Option α => (x (Prod.fst ga) (Prod.snd ga) : ℤ)) (principalTupleIntegers u)

variable (j : Fin m) (i : Fin (n j)) (hσ1 : σ j ≤ 1)
variable (henormous : S.value^(layerTailDegree m+1) < basisAxisScale (basis j) i)

local notation "centers" => allocatedIntegerProfileCenters (G := G) B R j i
local notation "widths" => allocatedIntegerProfileWidths (G := G) B R σ j i
local notation "scales" => allocatedIntegerProfileScales B U basis S j i
local notation "reindex" => allocatedKernelCoefficientEquiv (G := G) B j

end Erdos3.VectorPolynomial

end

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

end Erdos3.VectorPolynomial

end

section

namespace Erdos3

end Erdos3

namespace Erdos3.VectorPolynomial

open scoped BigOperators Matrix

variable {m : ℕ} {G : Type*} [Fintype G] {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U basis R σ)
variable {α : Type*} [Fintype α] [DecidableEq α] (x : G → IntegerScalarCubeBox α S.value)
variable (u : PrincipalAxisTuples (α := α) (allocatedGridAxis (I := I) U basis S.value)
  (allocatedPrincipalSides B U basis S))
variable {O : Fin m → Type*} [∀ j, Fintype (O j)] [∀ j, DecidableEq (O j)]
variable (rows : ∀ j, O j → Finset α) (j : Fin m)

local notation "grid" => allocatedGridAxis (I := I) U basis (LayerSamplerScale.value S)
local notation "sides" => allocatedPrincipalSides B U basis S
local notation "input" => partitionedPrincipalInput grid (fun g a => (g, a))
local notation "fixedInteger" => Sum.elim
  (fun ga : G × Option α => (x (Prod.fst ga) (Prod.snd ga) : ℤ)) (principalTupleIntegers u)
local notation "fixedReal" => Sum.elim
  (fun ga : G × Option α => ((x (Prod.fst ga) (Prod.snd ga) : ℤ) : ℝ) / (S.value : ℝ))
  (principalTupleNormalized (principalAxisLength grid sides) u)

variable (i : Fin (n j)) (s : O j ↪ BoundedIntegerExponent G (j.val+1))
variable (hA : ((scalarKernelIntegerJet x (j.val+1) (rows j)).submatrix id s).det ≠ 0)
variable (hσ1 : σ j ≤ 1) (henormous : S.value^(layerTailDegree m+1) < basisAxisScale (basis j) i)

local notation "height" => (basisAxisScale (basis j) i : ℝ)
local notation "heightPos" => Nat.cast_pos.mpr (basisAxisScale_pos (basis j) i)
local notation "kernelScale" => kernelJetCoefficientScale G (j.val+1) (S.value : ℝ) height
local notation "nonkernelScale" => fun d => height / monomialScale (layerSamplerBox B U basis S)
  (allocatedNonkernelExponent B j d)
local notation "centers" => allocatedIntegerProfileCenters (G := G) B R j i
local notation "widths" => allocatedIntegerProfileWidths (G := G) B R σ j i
local notation "reindex" => allocatedKernelCoefficientEquiv (G := G) B j
local notation "unitWidth" => allocatedUnitProfileWidth (R j) (σ j)
  (Fintype.card (BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val+1)))
local notation "radius" => NNReal.mk (R j) (le_of_lt (hR j))

variable [∀ j, DecidableEq (I j)] [∀ a, DecidableEq (B a)]
variable [DecidableEq (BoundedIntegerExponent G (j.val+1))]
variable [DecidableEq (AllocatedNonkernelCoefficient (G := G) B j)]

theorem allocatedIntegerKernel_residue_family
    (p : FiniteProbabilityWeights (PrincipalAxisTuples (α := α) (fun a => ¬grid a) sides))
    (modulus : ℕ)
    (residue : Matrix (O j) (AllocatedNonkernelCoefficient (G := G) B j) (ZMod modulus))
    (hperiod : integerScalarLattice (O j) (modulus : ℤ) ≤
      (scalarKernelIntegerJet x (j.val+1) (rows j)).mulVecLin.range)
    (hresidue : ∀ v, p.weight v ≠ 0 →
      integerResidueMatrix (allocatedNonkernelJetMatrix B U basis S x u rows j v) modulus = residue)
    {C V M b t ε : ℝ} (hC0 : 0 ≤ C) (hV0 : 0 ≤ V) (hM0 : 0 ≤ M)
    (ctrl : ∀ v, p.weight v ≠ 0 → CoefficientFiberControl
      (Matrix.fromCols (scalarKernelIntegerJet x (j.val+1) (rows j))
        (allocatedNonkernelJetMatrix B U basis S x u rows j v))
      (s.trans Function.Embedding.inl) (Sum.elim kernelScale nonkernelScale)
      height S.value (j.val+1) C V M)
    (hb : 0 ≤ b) (ht : 0 ≤ t) (hε : 0 < ε)
    (hM : M ≤ Real.exp b) (hV : V ≤ Real.exp b) (hC : C ≤ Real.exp b)
    (hRb : R j ≤ Real.exp b) (hwidth : unitWidth⁻¹ ≤ Real.exp t)
    (hlarge : coefficientReplacementScale
      (J := BoundedIntegerExponent G (j.val+1) ⊕ AllocatedNonkernelCoefficient (G := G) B j)
      (s.trans Function.Embedding.inl) b t ε S.value (j.val+1) ≤ height) :
    (∀ z, 0 ≤ allocatedIntegerKernelMask B U basis S x rows j modulus residue z ∧
      allocatedIntegerKernelMask B U basis S x rows j modulus residue z ≤ M) ∧
    ∀ v, p.weight v ≠ 0 → ∀ z,
      |height^Fintype.card (O j) *
          (allocatedIntegerKernelPMF B U basis hR hσ S x u v rows j i hσ1 henormous z).toReal -
        allocatedIntegerKernelMask B U basis S x rows j modulus residue z *
          allocatedIntegerKernelDensity B U basis S j i x u (rows j) s hA
            (principalTupleNormalized (principalAxisLength (fun a => ¬grid a) sides) v)
            (fun o => (z o : ℝ)/height)| ≤ ε := by
  sorry

end Erdos3.VectorPolynomial
end
end OAI
