-- Prove2me | Theorems.Thm_OAI_Erdos3_VectorPolynomial_allocatedLongJet_residue_coefficient_comparison
-- name    : OAI.Erdos3.VectorPolynomial.allocatedLongJet_residue_coefficient_comparison
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-10-09T23:33:44.396204+00:00
-- url     : https://prove2.me/theorems/bb6b367b-a23a-4820-94bb-a2282e003d5d
-- title:
--   Long-jet densities with a common residue match the masked normalized density
-- statement:
--   Fix the section data: a natural number $m$; a finite type $G$ with decidable equality; finite types $I_j$ with decidable equality and natural numbers $n_j$; finite types $B_a$ with decidable equality over the axes $a$ of `LayerSamplerAxis I n`; finite types $J_j$, real subspaces $U_j \subseteq \mathbb R^{J_j}$ and bases `basis j` (indexed by $\mathrm{Fin}\,n_j$) of the orthogonal complements of `euclideanSubspace (U j)`; real functions $R, \sigma$ on $\mathrm{Fin}\,m$ with $R_j > 0$ and $\sigma_j > 0$ for all $j$; a layer-sampler scale `S : LayerSamplerScale B U basis R σ`; a finite type $\alpha$ with decidable equality and a point $x : G \to $ `IntegerScalarCubeBox α S.value`; finite types $O_j$ with decidable equality; and maps $\mathrm{rows}_j : O_j \to \mathrm{Finset}\,\alpha$. Let grid be the predicate `allocatedGridAxis U basis S.value` and sides $=$ `allocatedPrincipalSides B U basis S`.
--
--   Let $M$ be a positive natural number; $\mathrm{selection} : \alpha \hookrightarrow G$ with `GoodScalarKernelTuple selection (1/M) M x`; assume $|\alpha| \le m+1$, each $\mathrm{rows}_j$ injective, $|\mathrm{rows}_j(o)| \le j+1$, and $\sigma_j \le 1$; let $P, e, \varepsilon$ be reals with $P \ge 0$, $e \ge 0$, $\varepsilon > 0$, $M \le e^P$, $R_j \le e^P$, $R_j^{-1} \le e^P$, $\sigma_j^{-1} \le e^P$, $|\texttt{BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j+1)}| + 1 \le e^P$ for all $j$, $\varepsilon^{-1} \le \exp(e)$, and $\exp(\texttt{allocatedKernelReplacementLog B α O P e}) \le$ `S.value`; let $\mathrm{modulus}$ be a natural number such that, for every $j$, $\mathrm{modulus}\cdot\mathbb Z^{O_j}$ is contained in the range of `scalarKernelIntegerJet x (j+1) (rows j)`; let $s_j : O_j \hookrightarrow$ `BoundedIntegerExponent G (j+1)` with the column-restricted matrices nonsingular ($hA$) and `fixedKernelInverseBound S.positive x (j+1) (rows j) (s j) (hA j) (1/M)` for all $j$; let $u$ be a grid tuple in `PrincipalAxisTuples grid sides`, $p$ finite probability weights on the non-grid tuples `PrincipalAxisTuples (¬ grid) sides`, and $\mathrm{residue}_j$ matrices over $\mathbb Z/\mathrm{modulus}$ (rows $O_j$, columns `AllocatedNonkernelCoefficient B j`) such that `integerResidueMatrix (allocatedNonkernelJetMatrix B U basis S x u rows j v) modulus` $= \mathrm{residue}_j$ for every $j$ and every $v$ with $p(v) \ne 0$; and let $z \in$ `AllocatedLongJetRows B U basis S O`. Put $C = \exp(\texttt{allocatedDensityLog B α O P})$, $C_M = $ `layerKernelIndexBound m M` $= M^{m 2^{m+1}}$, and let $N$ be the number of non-grid axes. Then
--   $$\Bigl| \sum_v p(v)\Bigl(\prod_a \lambda_a\Bigr)\,D_v(z) - \Bigl(\prod_a \mathrm{mask}_a(z_a)\Bigr) \sum_v p(v)\, \widetilde D(\nu(v))\bigl(\mathrm{coord}(z)\bigr) \Bigr| \le N\,\varepsilon\,(1 + C_M C + \varepsilon)^{N},$$
--   where products are over non-grid axes $a$, $\lambda_a = $ `allocatedLongJetOutputScale B U basis S a` (equal to $1$ on axes of the form $\langle j, \mathrm{inl}\ \_\rangle$ and to `basisAxisScale (basis j) i` $^{|O_j|}$ on $\langle j, \mathrm{inr}\ i\rangle$), $D_v = $ `allocatedLongJetDensity B U basis hR hσ S x u v rows s hA hσ1`, $\mathrm{mask}_a = $ `allocatedLongJetMask B U basis S x rows modulus residue a`, $\widetilde D(y) = $ `allocatedNormalizedLongJetDensity B U basis S x u rows s hA y`, $\nu(v) = $ `principalTupleNormalized (principalAxisLength (¬ grid) sides) v`, and $\mathrm{coord} = $ `allocatedLongJetRealCoordinates B U basis S`.
--
--   Lean: `OAI.Erdos3.VectorPolynomial.allocatedLongJet_residue_coefficient_comparison` in `lean/OAI/Combinatorics/Progressions/Estimates/AllocatedFiniteCoefficientL1.lean` (OpenAI); the definitions it uses are in the definitions bundles `OAIErdos3B132` of this split (and the bundles they import).
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/Progressions/Estimates/AllocatedFiniteCoefficientL1.lean#L28

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIErdos3B169
import Definitions.Def_OAIErdos3B174

namespace OAI

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators Matrix

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

theorem allocatedLongJet_residue_coefficient_comparison {M : ℕ} (hM : 0 < M)
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
    (z : AllocatedLongJetRows B U basis S O) :
    let C := Real.exp (allocatedDensityLog (G := G) B α O P)
    let CM : ℝ := layerKernelIndexBound m M
    let normalized := fun v => principalTupleNormalized (principalAxisLength (fun a => ¬grid a) sides) v
    |p.mean (fun v => (∏ a, allocatedLongJetOutputScale B U basis S (O := O) a) *
        allocatedLongJetDensity B U basis hR hσ S x u v rows s hA hσ1 z) -
      (∏ a, allocatedLongJetMask B U basis S x rows modulus residue a (z a)) *
        p.mean (fun v => allocatedNormalizedLongJetDensity B U basis S x u rows s hA
          (normalized v) (allocatedLongJetRealCoordinates B U basis S z))| ≤
      Fintype.card {a // ¬grid a} * ε * (1 + CM * C + ε)^Fintype.card {a // ¬grid a} := by
  sorry

end Erdos3.VectorPolynomial
end
end OAI
