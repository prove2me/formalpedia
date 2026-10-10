-- Prove2me | Theorems.Thm_OAI_Erdos3_VectorPolynomial_allocatedLongJet_residue_coefficient_l1
-- name    : OAI.Erdos3.VectorPolynomial.allocatedLongJet_residue_coefficient_l1
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-10-09T23:36:02.187632+00:00
-- url     : https://prove2.me/theorems/232f8f56-add5-4dcd-846a-66d8daeaa0e3
-- title:
--   The long-jet density mixture is L1-close to its residue profile density
-- statement:
--   Fix $m \in \mathbb N$, a finite type $G$ with decidable equality, finite types $I_j$ ($j \in \mathrm{Fin}\,m$), $n : \mathrm{Fin}\,m \to \mathbb N$, finite types $B_a$ indexed by $a \in$ `LayerSamplerAxis I n` (the sigma type $\Sigma_j\, I_j \oplus \mathrm{Fin}(n_j)$), finite types $J_j$ with subspaces $U_j \le \mathbb R^{J_j}$, bases $\mathrm{basis}_j$ (indexed by $\mathrm{Fin}(n_j)$) of the orthogonal complement of `euclideanSubspace (U j)`, reals $R_j > 0$ and $\sigma_j > 0$, and a `LayerSamplerScale` $S$ (a structure bundling a positive natural number $S.\mathrm{value}$ with width and gap inequalities). Let $\alpha$ be a finite type with decidable equality, $x : G \to$ `IntegerScalarCubeBox α S.value` (integer vectors indexed by $\mathrm{Option}\,\alpha$ with entries in $[-S.\mathrm{value}, S.\mathrm{value})$), $O_j$ finite types with decidable equality, and $\mathrm{rows}_j : O_j \to \mathrm{Finset}\,\alpha$. Write grid for `allocatedGridAxis U basis S.value` (a predicate on `LayerSamplerAxis I n`) and sides for `allocatedPrincipalSides B U basis S`. Let $M \in \mathbb N$ with $M > 0$; let $\mathrm{selection} : \alpha \hookrightarrow G$ be an embedding with `GoodScalarKernelTuple selection (1/M) M x`; assume $|\alpha| \le m+1$, each $\mathrm{rows}_j$ injective, $|\mathrm{rows}_j(o)| \le j+1$ for all $j, o$, and $\sigma_j \le 1$ for all $j$. Let $P, e, \varepsilon$ be reals with $0 \le P$, $0 \le e$, $0 < \varepsilon$, $M \le \exp P$, and for all $j$: $R_j \le \exp P$, $R_j^{-1} \le \exp P$, $\sigma_j^{-1} \le \exp P$, and $|$`BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j+1)`$| + 1 \le \exp P$; assume $\varepsilon^{-1} \le \exp(e)$ and $\exp($`allocatedKernelReplacementLog B α O P e`$) \le S.\mathrm{value}$. Let $\mathrm{modulus} \in \mathbb N$ with `integerScalarLattice (O j) modulus` (the multiples of modulus in $\mathbb Z^{O_j}$) contained in the range of the integer matrix `scalarKernelIntegerJet x (j+1) (rows j)` for every $j$. Let $s_j : O_j \hookrightarrow$ `BoundedIntegerExponent G (j+1)` be embeddings such that the square submatrix of `scalarKernelIntegerJet x (j+1) (rows j)` on the columns $s_j$ has nonzero determinant ($h_A$), and assume `fixedKernelInverseBound S.positive x (j+1) (rows j) (s j) (hA j) (1/M)` for every $j$. Let $u$ be in `PrincipalAxisTuples grid sides`, let $p$ be `FiniteProbabilityWeights` (a probability vector) on `PrincipalAxisTuples (¬grid) sides`, and let $\mathrm{residue}_j$ be matrices over $\mathbb Z/\mathrm{modulus}$ indexed by $O_j \times$ `AllocatedNonkernelCoefficient B j` such that for every $v$ with $p(v) \ne 0$ and every $j$, the reduction mod modulus of `allocatedNonkernelJetMatrix B U basis S x u rows j v` equals $\mathrm{residue}_j$. Put $C = \exp($`allocatedDensityLog B α O P`$)$, $C_M =$ `layerKernelIndexBound m M` $= M^{m 2^{m+1}}$, $T = \exp($`allocatedJetSupportLog B α O P`$)$, and let $\mathrm{proxy}(z) = \sum_v p(v)\,$`allocatedNormalizedLongJetDensity B U basis S x u rows s hA (principalTupleNormalized (principalAxisLength (¬grid) sides) v) z`. Then (1) `allocatedLongProfileDensity B U basis S x rows modulus residue proxy` is integrable with respect to the measure `allocatedLongJetReference B U basis S O`, and (2), writing $\mu$ for that measure and $N = |\{a \mid \neg\,\mathrm{grid}\,a\}|$,
--   $$\int \Bigl|\textstyle\sum_v p(v)\,\texttt{allocatedLongJetDensity}(\ldots v \ldots)(z) - \texttt{allocatedLongProfileDensity}(\ldots,\mathrm{proxy})(z)\Bigr|\,d\mu(z) \le (2T+1)^{K}\, N\varepsilon\,(1 + C_M C + \varepsilon)^{N},$$
--   where the density inside is `allocatedLongJetDensity B U basis hR hσ S x u v rows s hA hσ1` and $K$ is the cardinality of $\Sigma_{a \in \texttt{LayerSamplerAxis I n}}\, O_{a.1}$.
--
--   Lean: `OAI.Erdos3.VectorPolynomial.allocatedLongJet_residue_coefficient_l1` in `lean/OAI/Combinatorics/Progressions/Lattices/AllocatedResidueCoefficientL1.lean` (OpenAI); the definitions it uses are in the definitions bundles `OAIErdos3B169`, `OAIErdos3B176` of this split (and the bundles they import).
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/Progressions/Lattices/AllocatedResidueCoefficientL1.lean#L29

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIErdos3B169
import Definitions.Def_OAIErdos3B176

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
variable {α : Type*} [Fintype α] [DecidableEq α] (x : G → IntegerScalarCubeBox α S.value)
variable [DecidableEq G] [∀ j, DecidableEq (I j)] [∀ a, DecidableEq (B a)]
variable {O : Fin m → Type*} [∀ j, Fintype (O j)] [∀ j, DecidableEq (O j)]
variable [∀ j : Fin m, DecidableEq (BoundedIntegerExponent G (j.val+1))]
variable [∀ j : Fin m, DecidableEq (AllocatedNonkernelCoefficient (G := G) B j)]
variable (rows : ∀ j, O j → Finset α)

local notation "grid" => allocatedGridAxis (I := I) U basis (LayerSamplerScale.value S)
local notation "sides" => allocatedPrincipalSides B U basis S

theorem allocatedLongJet_residue_coefficient_l1 {M : ℕ} (hM : 0 < M)
    (selection : α ↪ G) (hx : GoodScalarKernelTuple selection (1/(M : ℝ)) M x)
    (hq : Fintype.card α ≤ m+1) (hinj : ∀ j, Function.Injective (rows j))
    (hrows : ∀ j o, (rows j o).card ≤ j.val+1) (hσ1 : ∀ j, σ j ≤ 1)
    {P e ε : ℝ} (hP : 0 ≤ P) (he : 0 ≤ e) (hε : 0 < ε)
    (hMP : (M : ℝ) ≤ Real.exp P) (hRP : ∀ j, R j ≤ Real.exp P)
    (hRi : ∀ j, (R j)⁻¹ ≤ Real.exp P) (hσi : ∀ j, (σ j)⁻¹ ≤ Real.exp P)
    (hcount : ∀ j : Fin m,
      (Fintype.card (BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val+1)) : ℝ)+1 ≤ Real.exp P)
    (hεe : ε⁻¹ ≤ Real.exp e)
    (hlarge : Real.exp (allocatedKernelReplacementLog (G := G) B α O P e) ≤ S.value)
    (modulus : ℕ)
    (hperiod : ∀ j, integerScalarLattice (O j) (modulus : ℤ) ≤
      (scalarKernelIntegerJet x (j.val+1) (rows j)).mulVecLin.range)
    (s : ∀ j, O j ↪ BoundedIntegerExponent G (j.val+1))
    (hA : ∀ j, ((scalarKernelIntegerJet x (j.val+1) (rows j)).submatrix id (s j)).det ≠ 0)
    (hi : ∀ j : Fin m, fixedKernelInverseBound S.positive x (j.val+1) (rows j) (s j) (hA j) (1/(M : ℝ)))
    (u : PrincipalAxisTuples (α := α) grid sides)
    (p : FiniteProbabilityWeights (PrincipalAxisTuples (α := α) (fun a => ¬grid a) sides))
    (residue : ∀ j, Matrix (O j) (AllocatedNonkernelCoefficient (G := G) B j) (ZMod modulus))
    (hr : ∀ v, p.weight v ≠ 0 → ∀ j,
      integerResidueMatrix (allocatedNonkernelJetMatrix B U basis S x u rows j v) modulus = residue j)
 :
    let C := Real.exp (allocatedDensityLog (G := G) B α O P)
    let CM : ℝ := layerKernelIndexBound m M
    let T := Real.exp (allocatedJetSupportLog (G := G) B α O P)
    let normalized := fun v => principalTupleNormalized (principalAxisLength (fun a => ¬grid a) sides) v
    let proxy := fun z => p.mean (fun v => allocatedNormalizedLongJetDensity B U basis S x u rows s hA (normalized v) z)
    Integrable (allocatedLongProfileDensity B U basis S x rows modulus residue proxy)
      (allocatedLongJetReference B U basis S O) ∧
    (∫ z, |p.mean (fun v => allocatedLongJetDensity B U basis hR hσ S x u v rows s hA hσ1 z) -
        allocatedLongProfileDensity B U basis S x rows modulus residue proxy z|
      ∂allocatedLongJetReference B U basis S O) ≤
      (2*T+1)^Fintype.card (Σ a : LayerSamplerAxis I n, O a.1) *
        (Fintype.card {a // ¬grid a} * ε * (1 + CM * C + ε)^Fintype.card {a // ¬grid a}) := by
  sorry

end Erdos3.VectorPolynomial
end
end OAI
