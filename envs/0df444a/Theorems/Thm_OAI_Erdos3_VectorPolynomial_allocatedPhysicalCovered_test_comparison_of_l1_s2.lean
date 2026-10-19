-- Prove2me | Theorems.Thm_OAI_Erdos3_VectorPolynomial_allocatedPhysicalCovered_test_comparison_of_l1_s2
-- name    : OAI.Erdos3.VectorPolynomial.allocatedPhysicalCovered_test_comparison_of_l1_s2
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-18T04:21:20.624643+00:00
-- url     : https://prove2.me/theorems/76494beb-79ba-4945-b9ff-d0e476ac5715
-- title:
--   An L1 approximation of the mixed long-jet density controls the covered physical test mean
-- statement:
--   **Setting.** Let $m$ be a natural number, $G$ a finite type, $I : \mathrm{Fin}\ m \to \mathrm{Type}$ a family of finite types with decidable equality, $n : \mathrm{Fin}\ m \to \mathbb{N}$, $B$ a family of finite types with decidable equality indexed by `LayerSamplerAxis I n`, $J$ a family of finite types indexed by $\mathrm{Fin}\ m$, $U_j$ a real subspace of $J_j \to \mathbb{R}$, and $b_j$ a basis indexed by $\mathrm{Fin}\ (n\ j)$ of the orthogonal complement of `euclideanSubspace (U j)` whose $\mathbb{Z}$-span is `projectedIntegerLattice (euclideanSubspace (U j))`. Let $R, \sigma : \mathrm{Fin}\ m \to \mathbb{R}$ with $0 < R_j$, $0 < \sigma_j \le 1$ for all $j$, and $S$ a `LayerSamplerScale B U b R σ` (defined by OpenAI, with positive natural number `S.value`). Let $\alpha$ be a finite type with decidable equality, $x : G \to$ `IntegerScalarCubeBox α S.value`, $u$ an element of `PrincipalAxisTuples (allocatedGridAxis U b S.value) (allocatedPrincipalSides B U b S)` (integer tuples on the grid axes) and $v_0$ an element of the corresponding type for the non-grid axes (`fun a => ¬ allocatedGridAxis U b S.value a`); these are defined by OpenAI. Let $O, Q : \mathrm{Fin}\ m \to \mathrm{Type}$ be families of finite types ($O_j$ with decidable equality), $\mathrm{rows}_j : O_j \to \mathrm{Finset}\ \alpha$, $o_j$ an orthonormal basis of `euclideanSubspace (U j)` indexed by $I\ j$, $bW_j$ a $\mathbb{Z}$-basis indexed by $Q_j$ of `latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))`, and $d$ a nonzero natural number. Let $s_j$ be an embedding of $O_j$ into `BoundedIntegerExponent G (j + 1)` such that the columns $s_j(o)$ of `scalarKernelIntegerJet x (j + 1) (rows j)` form a matrix with nonzero determinant (hypothesis $hA_j$).
--
--   **Hypotheses.** Let `weights` be a `FiniteProbabilityWeights` (probability weights, defined by OpenAI) on the non-grid tuples, and let $\mathrm{period}$ be a natural number such that:
--   - for every $j$, the lattice $\mathrm{period}\cdot\mathbb{Z}^{O_j}$ (`integerScalarLattice (O j) period`) is contained in the image of the integer linear map given by `scalarKernelIntegerJet x (j + 1) (rows j)`;
--   - for every non-grid tuple $v$ with nonzero weight, `principalResidueLabel period v = principalResidueLabel period v₀` (the entries of $v$ and $v_0$ agree modulo $\mathrm{period}$).
--
--   Let $F$ be a complex-valued function on `AllocatedFrozenCoefficients B U b S × EuclideanJetLayers U O`. Let $g$ be a real-valued function on `AllocatedLongJetRows B U b S O`, integrable with respect to the reference measure $\mu$ = `allocatedLongJetReference B U b S O` (a product measure defined by OpenAI), and let $\varepsilon$ be a real number with
--   $$\int \Bigl| \texttt{weights.mean}\bigl(v \mapsto \rho_v(z)\bigr) - g(z) \Bigr|\, d\mu(z) \le \varepsilon,$$
--   where $\rho_v$ = `allocatedLongJetDensity B U b hR hσ S x u v rows s hA hσ1` (a probability density with respect to $\mu$, defined by OpenAI). Suppose $F$ is measurable and $\lVert F(p) \rVert \le 1$ for all $p$.
--
--   **Conclusion.** Let $\mathrm{actual}$ be the integral, over pairs $(a, r)$ distributed according to the product of `allocatedCoefficientSource B U b hR hσ S` (the law of the coefficient sample arrays) and the uniform distribution on `CoefficientDeckResidues Q d`, of
--   $$\texttt{weights.complexMean}\Bigl(v \mapsto F\bigl(\pi_1(\texttt{allocatedCoefficientSplit B U b S}\ a),\ \texttt{euclideanCoefficientJetMap U}\ (\mathrm{root}_v)\ (\mathrm{dirs}_v)\ \mathrm{rows}\ (\texttt{canonicalCoefficientDeckSample U bW b hb o d}\ a\ r)\bigr)\Bigr),$$
--   where $\pi_1$ is the first component, $\mathrm{root}_v$ = `allocatedPhysicalCubeRoot B U b S (fun _ => 0) x w` and $\mathrm{dirs}_v$ = `allocatedPhysicalCubeDirections B U b S x w` with $w$ = `principalAxisJoin grid u v` (the full tuple obtained by joining $u$ and $v$), all defined by OpenAI. Then
--   $$\Bigl\lVert \mathrm{actual} - \int \int g(z)\cdot \texttt{test}(a_0, z)\, d\mu(z)\, d\nu(a_0) \Bigr\rVert \le \varepsilon,$$
--   where $\nu$ = `allocatedFrozenCoefficientSource B U b hR hσ S` (a product probability measure on the frozen coefficients) and `test` = `allocatedCoveredFixedTest B U b S x u v₀ rows Q hb o bW d F`, a complex-valued function defined by OpenAI.
--
--   Lean: `OAI.Erdos3.VectorPolynomial.allocatedPhysicalCovered_test_comparison_of_l1_s2`, which states OpenAI's `OAI.Erdos3.VectorPolynomial.allocatedPhysicalCovered_test_comparison_of_l1` (in `lean/OAI/Combinatorics/Progressions/Estimates/AllocatedSlicedCoveredComparison.lean`); the definitions it uses are in the definitions bundle `OAIE3v2B194` of version 2 of this split (and the bundles they import).
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/Progressions/Estimates/AllocatedSlicedCoveredComparison.lean (declaration OAI.Erdos3.VectorPolynomial.allocatedPhysicalCovered_test_comparison_of_l1)

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIE3v2B194

section

namespace OAI

section

namespace Erdos3.VectorPolynomial

open MeasureTheory Module Submodule
open scoped BigOperators Classical

variable {m : ℕ} {G : Type*} [Fintype G] [DecidableEq G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U b R σ)
variable {α : Type*} [Fintype α] [DecidableEq α] (x : G → IntegerScalarCubeBox α S.value)
variable (u : PrincipalAxisTuples (α := α) (allocatedGridAxis (I := I) U b S.value)
  (allocatedPrincipalSides B U b S))
variable (v₀ : PrincipalAxisTuples (α := α) (fun a => ¬allocatedGridAxis (I := I) U b S.value a)
  (allocatedPrincipalSides B U b S))
variable {O : Fin m → Type*} [∀ j, Fintype (O j)] [∀ j, DecidableEq (O j)]
variable (rows : ∀ j, O j → Finset α)
variable (Q : Fin m → Type*) [∀ j, Fintype (Q j)]
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable (bW : ∀ j, Basis (Q j) ℤ
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
variable (d : ℕ) [NeZero d]
variable (s : ∀ j, O j ↪ BoundedIntegerExponent G (j.val + 1))
variable (hA : ∀ j, ((scalarKernelIntegerJet x (j.val + 1) (rows j)).submatrix id (s j)).det ≠ 0)
variable (hσ1 : ∀ j, σ j ≤ 1)
variable [∀ j, DecidableEq (I j)] [∀ a, DecidableEq (B a)]
variable (weights : FiniteProbabilityWeights (PrincipalAxisTuples (α := α)
  (fun a => ¬allocatedGridAxis (I := I) U b S.value a) (allocatedPrincipalSides B U b S)))
variable (period : ℕ) (hperiod : ∀ j, integerScalarLattice (O j) (period : ℤ) ≤
  (scalarKernelIntegerJet x (j.val + 1) (rows j)).mulVecLin.range)
variable (hresidue : ∀ v, weights.weight v ≠ 0 → principalResidueLabel period v = principalResidueLabel period v₀)
variable (F : AllocatedFrozenCoefficients B U b S × EuclideanJetLayers U O → ℂ)

local notation "grid" => allocatedGridAxis (I := I) U b (LayerSamplerScale.value S)
local notation "source" => allocatedCoefficientSource B U b hR hσ S
local notation "frozenSource" => allocatedFrozenCoefficientSource B U b hR hσ S
local notation "reference" => allocatedLongJetReference B U b S O
local notation "density" => (fun v z => allocatedLongJetDensity B U b hR hσ S x u v rows s hA hσ1 z)
local notation "root" v => allocatedPhysicalCubeRoot B U b S (fun _ => 0) x (principalAxisJoin grid u v)
local notation "dirs" v => allocatedPhysicalCubeDirections B U b S x (principalAxisJoin grid u v)
local notation "deck" => PMF.uniformOfFintype (CoefficientDeckResidues (K := LayerSamplerVariables G I n B) Q d)
local notation "test" => allocatedCoveredFixedTest B U b S x u v₀ rows Q hb o bW d F
local notation "actual" => (∫ p, weights.complexMean (fun v => F (Prod.fst ((allocatedCoefficientSplit B U b S) (Prod.fst p)),
  euclideanCoefficientJetMap U (root v) (dirs v) rows
    (canonicalCoefficientDeckSample U bW b hb o d (Nat.pos_of_ne_zero (NeZero.ne d)) (Prod.fst p) (Prod.snd p))))
    ∂(Measure.prod source (PMF.toMeasure deck)))

include hperiod hresidue

omit [DecidableEq G] in
theorem allocatedPhysicalCovered_test_comparison_of_l1_s2
    (g : AllocatedLongJetRows B U b S O → ℝ) (hg : Integrable g reference)
    {ε : ℝ} (he : (∫ z, |weights.mean (fun v => density v z) - g z| ∂reference) ≤ ε)
    (hF : Measurable F) (hbound : ∀ p, ‖F p‖ ≤ 1) :
    ‖actual - ∫ a₀, ∫ z, (g z : ℂ) * test a₀ z ∂reference ∂frozenSource‖ ≤ ε := by
  sorry

end Erdos3.VectorPolynomial

end

end OAI
end
