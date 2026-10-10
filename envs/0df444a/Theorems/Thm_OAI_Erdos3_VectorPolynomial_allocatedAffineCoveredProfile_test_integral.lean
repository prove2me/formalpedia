-- Prove2me | Theorems.Thm_OAI_Erdos3_VectorPolynomial_allocatedAffineCoveredProfile_test_integral
-- name    : OAI.Erdos3.VectorPolynomial.allocatedAffineCoveredProfile_test_integral
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-10-09T23:58:41.746864+00:00
-- url     : https://prove2.me/theorems/962502cf-5ad7-4e8d-b9a1-c84de5206ba7
-- title:
--   Covered fixed-test integral of the affine profile as a torus integral of its density
-- statement:
--   Fix the section data: a natural number $m$; finite types $G$ and $I_j$, natural numbers $n_j$, finite types $B_a$ with decidable equality over the axes $a$ of `LayerSamplerAxis I n`; finite types $J_j$, real subspaces $U_j \subseteq \mathbb R^{J_j}$ with $V_j = $ `euclideanSubspace (U j)` and $W_j = \mathbb Z^{J_j} \cap V_j$ (`latticeSection`), and bases `basis j` (indexed by $\mathrm{Fin}\,n_j$) of $V_j^\perp$; real functions $R, \sigma$ on $\mathrm{Fin}\,m$; a layer-sampler scale `S : LayerSamplerScale B U basis R σ`; a finite type $\alpha$ with decidable equality; finite types $O_j$ and maps $\mathrm{rows}_j : O_j \to \mathrm{Finset}\,\alpha$; a point $x : G \to $ `IntegerScalarCubeBox α S.value`; a grid tuple $u$ in `PrincipalAxisTuples (allocatedGridAxis U basis S.value) (allocatedPrincipalSides B U basis S)`; the hypothesis $R_j > 0$ for all $j$; $\rho \in \mathbb R_{\ge 0}$; real functions $\mathrm{center}, \mathrm{width}$ on `PrincipalAxisParameter (¬ grid)`, where grid is the predicate `allocatedGridAxis U basis S.value`; the hypothesis $\sigma_j > 0$ for all $j$; a non-grid tuple $v_0$ in `PrincipalAxisTuples (¬ grid) (allocatedPrincipalSides B U basis S)`; finite types $Q_j$; the hypothesis $hb$ that the $\mathbb Z$-span of `basis j` is `projectedIntegerLattice V_j`; orthonormal bases $o_j$ of $V_j$ indexed by $I_j$; $\mathbb Z$-bases $bW_j$ of $W_j$ indexed by $Q_j$; a positive natural number $d$; the assumption that each $W_j$ is a full lattice in $V_j$; and additively left-invariant probability measures $\nu_j$ on the tori $V_j/W_j$. Let ideal be `diagonalImageDensity (q ↦ R_{layer(q)}) (activeAveragedSlicedProfileIdeal (G × Option α) (layerSamplerDegree I n) grid rows ρ center width)`.
--
--   Assume $0 < \rho \le 1$ and $|\mathrm{center}(i)| + |\mathrm{width}(i)| \le 1$ for all $i$; let $P$ be real with $R_j \le e^P$ and $R_j^{-1} \le e^P$; let $\mathrm{modulus}$ be a natural number and $\mathrm{residue}_j$ matrices over $\mathbb Z/\mathrm{modulus}$ with rows $O_j$ and columns `AllocatedNonkernelCoefficient B j`; let $C_{\mathrm{mask}} \ge 1$ with $0 \le$ `allocatedIntegerKernelMask B U basis S x rows j modulus (residue j) z` $\le C_{\mathrm{mask}}$ for all $j, z$; assume $\sigma_j \le 1$; let $T : \mathrm{Fin}\,m \to \mathbb R$ with `partitionedIdealRadius α m` $+ 1 \le T_j$ (where `partitionedIdealRadius α k` $= 1/4 + 2^{|\alpha|}(|\alpha|+1)^k$) and $|\texttt{BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j+1)}| \cdot 2^{|\alpha|}(|\alpha|+1)^{j+1} \le T_j$; let $C_j \ge 0$ with $\|(\texttt{normalizedOrthogonalChart}\ V_j\ (\texttt{basis}\ j))^{-1} v\| \le C_j\|v\|$ for all $v$ and $C_j\,(|I_j| + 1)\,T_j R_j \le 1/4$; and let $F : $ `EuclideanJetLayers U O` $\to \mathbb C$ be measurable with $\|F(z)\| \le C_F$ for all $z$. With $f = $ `allocatedLongProfileDensity B U basis S x rows modulus residue ideal`,
--   $$\int\!\!\int f(z)\cdot\texttt{allocatedCoveredFixedTest B U basis S x u v₀ rows Q hb o bW d}\,(p \mapsto F(p_2))\,(a_0, z) = \int g(y)\,F(y)\,d\Bigl(\prod_j \prod_{O_j} \nu_j\Bigr)(y),$$
--   where the inner integral is in $z$ against `allocatedLongJetReference B U basis S O`, the outer in $a_0$ against `allocatedFrozenCoefficientSource B U basis hR hσ S`, and $g = $ `allocatedCoveredProfileDensity B U basis hR hσ S x u v₀ rows hb o bW d Ω f` with $\Omega_{j,t}$ the closed quarter box $\{x : |x_i| \le 1/4\}$ for every $j$ and $t \in O_j$.
--
--   Lean: `OAI.Erdos3.VectorPolynomial.allocatedAffineCoveredProfile_test_integral` in `lean/OAI/Combinatorics/Progressions/Lattices/AllocatedAffineProfileMeanTransport.lean` (OpenAI); the definitions it uses are in the definitions bundles `OAIErdos3B140`, `OAIErdos3B169`, `OAIErdos3B170` of this split (and the bundles they import).
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/Progressions/Lattices/AllocatedAffineProfileMeanTransport.lean#L143

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIErdos3B140
import Definitions.Def_OAIErdos3B169
import Definitions.Def_OAIErdos3B170

namespace OAI

section

namespace Erdos3
open scoped NNReal

end Erdos3

end

section

namespace Erdos3.VectorPolynomial
open MeasureTheory
open scoped BigOperators NNReal Classical

variable {m : ℕ} {G : Type*} [Fintype G] {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j)
variable (S : LayerSamplerScale (G := G) B U basis R σ)
variable {α : Type*} [Fintype α] [DecidableEq α] (x : G → IntegerScalarCubeBox α S.value)
variable {O : Fin m → Type*} [∀ j, Fintype (O j)] (rows : ∀ j, O j → Finset α)

local notation "grid" => allocatedGridAxis (I := I) U basis S.value
local notation "input" => PrincipalAxisParameter (B := B) (h := layerSamplerDegree I n)
  (α := α) (fun a => ¬grid a)
local notation "output" => (Σ a : {a // ¬grid a}, O (Sigma.fst (Subtype.val a)))

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open MeasureTheory Module Submodule
open scoped Classical NNReal

variable {m : ℕ} {G : Type*} [Fintype G] {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*)
variable [∀ a, Fintype (B a)] [∀ a, DecidableEq (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U basis R σ)
variable {α : Type*} [Fintype α] [DecidableEq α]
variable {O : Fin m → Type*} [∀ j, Fintype (O j)]
variable (rows : ∀ j, O j → Finset α)
variable (x : G → IntegerScalarCubeBox α S.value)
variable (u : PrincipalAxisTuples (α := α) (allocatedGridAxis (I := I) U basis S.value)
  (allocatedPrincipalSides B U basis S))

local notation "grid" => allocatedGridAxis (I := I) U basis S.value
local notation "degree" => layerSamplerDegree I n
local notation "Jet" => (Σ a : {a // ¬grid a}, O (Sigma.fst (Subtype.val a)))
variable (hR : ∀ j, 0 < R j)
variable (ρ : ℝ≥0)
variable (center width : PrincipalAxisParameter (B := B) (h := layerSamplerDegree I n)
  (α := α) (fun a => ¬allocatedGridAxis (I := I) U basis S.value a) → ℝ)

variable (hσ : ∀ j, 0 < σ j)
variable (v₀ : PrincipalAxisTuples (α := α) (fun a => ¬allocatedGridAxis (I := I) U basis S.value a)
  (allocatedPrincipalSides B U basis S))
variable (Q : Fin m → Type*) [∀ j, Fintype (Q j)]
variable (hb : ∀ j, span ℤ (Set.range (basis j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable (bW : ∀ j, Basis (Q j) ℤ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
variable (d : ℕ) [NeZero d]
variable [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]
variable (ν : ∀ j, Measure (euclideanSubspace (U j) ⧸
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))).toAddSubgroup))
variable [∀ j, (ν j).IsAddLeftInvariant] [∀ j, IsProbabilityMeasure (ν j)]

local notation "jetRows" => O
local notation "ideal" => diagonalImageDensity (fun q : Jet => R (Sigma.fst (Subtype.val (Sigma.fst q))))
  (activeAveragedSlicedProfileIdeal (G := G) (B := B) (G × Option α)
    (layerSamplerDegree I n) grid (fun a => rows (Sigma.fst (Subtype.val a))) ρ center width)
local notation "reference" => allocatedLongJetReference B U basis S jetRows

omit [∀ a, DecidableEq (B a)] in
theorem allocatedAffineCoveredProfile_test_integral
    [∀ a, DecidableEq (B a)]
    (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (hw : ∀ i, |center i| + |width i| ≤ 1)
    {P : ℝ}
    (hRbound : ∀ j, R j ≤ Real.exp P) (hInv : ∀ j, (R j)⁻¹ ≤ Real.exp P)
    (modulus : ℕ)
    (residue : ∀ j, Matrix (O j) (AllocatedNonkernelCoefficient (G := G) B j) (ZMod modulus))
    {Cmask : ℝ} (hCmask : 1 ≤ Cmask)
    (hmask : ∀ j z, 0 ≤ allocatedIntegerKernelMask B U basis S x rows j modulus (residue j) z ∧
      allocatedIntegerKernelMask B U basis S x rows j modulus (residue j) z ≤ Cmask)
    (hσ1 : ∀ j, σ j ≤ 1)
    (T : Fin m → ℝ) (hT : ∀ j, partitionedIdealRadius α m + 1 ≤ T j)
    (hsource : ∀ j, (Fintype.card (BoundedCoefficientExponent
      (LayerSamplerVariables G I n B) (j.val + 1)) : ℝ) *
        ((2 : ℝ) ^ Fintype.card α * ((Fintype.card α : ℝ) + 1) ^ (j.val + 1)) ≤ T j)
    (C : Fin m → ℝ) (hC : ∀ j, 0 ≤ C j)
    (hchart : ∀ j v, ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (basis j)).symm v‖ ≤ C j * ‖v‖)
    (hbudget : ∀ j, C j * (((Fintype.card (I j) : ℝ) + 1) * (T j * R j)) ≤ 1 / 4)
    (F : EuclideanJetLayers U jetRows → ℂ) (hF : Measurable F)
    {CF : ℝ} (hFb : ∀ z, ‖F z‖ ≤ CF) :
    let f := allocatedLongProfileDensity B U basis S x rows modulus residue ideal
    (∫ a₀, ∫ z, (f z : ℂ) * allocatedCoveredFixedTest B U basis S x u v₀ rows
      Q hb o bW d (fun p => F p.2) a₀ z ∂reference ∂allocatedFrozenCoefficientSource B U basis hR hσ S) =
      ∫ y, (allocatedCoveredProfileDensity B U basis hR hσ S x u v₀ rows hb o bW d
        (fun j (_ : O j) => standardLatticeClosedQuarterBox (J j)) f y : ℂ) * F y
          ∂Measure.pi (fun j => Measure.pi (fun _ : O j => ν j)) := by
  sorry

end Erdos3.VectorPolynomial
end
end OAI
