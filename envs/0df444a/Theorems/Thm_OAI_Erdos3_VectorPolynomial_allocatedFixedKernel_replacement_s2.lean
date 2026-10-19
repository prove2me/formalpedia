-- Prove2me | Theorems.Thm_OAI_Erdos3_VectorPolynomial_allocatedFixedKernel_replacement_s2
-- name    : OAI.Erdos3.VectorPolynomial.allocatedFixedKernel_replacement_s2
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-17T11:53:49.922989+00:00
-- url     : https://prove2.me/theorems/0b87d394-960d-416f-ae93-7ce27bd1ca80
-- title:
--   For a good scalar kernel tuple, the rescaled allocated integer kernel PMF is uniformly close to a residue mask times the continuous kernel density
-- statement:
--   All named objects below are defined by OpenAI. Let $m$ be a natural number, $G$ a finite type, and for $j < m$ let $I_j$, $J_j$ be finite types and $n_j$ natural numbers; let $B_a$ be finite types indexed by `LayerSamplerAxis I n`. For each $j$ let $U_j$ be a real subspace of $\mathbb{R}^{J_j}$ and `basis j` a basis, indexed by $\{0,\dots,n_j-1\}$, of the orthogonal complement of the Euclidean copy of $U_j$. Let $R_j, \sigma_j$ be real numbers with $R_j > 0$ and $\sigma_j > 0$ for all $j$, and let $S$ be a `LayerSamplerScale B U basis R σ` (with scale value `S.value`, a positive natural number). Let $\alpha$ be a finite type with decidable equality and $x : G \to$ `IntegerScalarCubeBox α S.value` (each $x(g)$ is an integer vector indexed by `Option α` with entries in $[-\mathrm{S.value}, \mathrm{S.value})$). Let $O_j$ be finite types and `rows j : O j → Finset α`. (Decidable equality is assumed on all the index types involved.) Write grid for `allocatedGridAxis U basis S.value` and sides for `allocatedPrincipalSides B U basis S`.
--
--   Let $M$ be a natural number and $P, e, \varepsilon$ real numbers, and assume:
--   - $0 < M$;
--   - there is an embedding `selection` of $\alpha$ into $G$ such that `GoodScalarKernelTuple selection (1/M) M x` holds (the normalized scalar cube minor of $x$ along `selection` has absolute value greater than $1/M$, and the range of the scalar cube difference matrix has bounded period $M$);
--   - $|\alpha| \le m+1$; each `rows j` is injective; $|\mathrm{rows}\ j\ o| \le j+1$ for all $j, o$; $\sigma_j \le 1$ for all $j$;
--   - $0 \le P$, $0 \le e$, $0 < \varepsilon$, $M \le e^P$, and for every $j$: $R_j \le e^P$, $R_j^{-1} \le e^P$, $\sigma_j^{-1} \le e^P$, and $|\texttt{BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j+1)}| + 1 \le e^P$;
--   - $\varepsilon^{-1} \le e^{e}$;
--   - $\exp(\texttt{allocatedKernelReplacementLog B α O P e}) \le \mathrm{S.value}$;
--   - `modulus` is a natural number such that for every $j$ the lattice `integerScalarLattice (O j) modulus` $= \mathrm{modulus}\cdot\mathbb{Z}^{O_j}$ is contained in the range of the integer matrix `scalarKernelIntegerJet x (j+1) (rows j)`;
--   - `s j` is an embedding of $O_j$ into `BoundedIntegerExponent G (j+1)` such that (`hA`) for every $j$ the square submatrix of `scalarKernelIntegerJet x (j+1) (rows j)` with columns selected by `s j` has nonzero determinant, and (`hi`) for every $j$, `fixedKernelInverseBound S.positive x (j+1) (rows j) (s j) (hA j) (1/M)` holds.
--
--   Then for every $u$ in `PrincipalAxisTuples grid sides` (grid principal-axis tuples), every finite probability distribution $p$ on `PrincipalAxisTuples (fun a => ¬ grid a) sides` (active principal-axis tuples), and every family of residue matrices `residue j` over $\mathbb{Z}/\mathrm{modulus}$ indexed by $O_j \times$ `AllocatedNonkernelCoefficient B j`: if for every $v$ with $p(v) \ne 0$ and every $j$ the reduction mod `modulus` (`integerResidueMatrix`) of `allocatedNonkernelJetMatrix B U basis S x u rows j v` equals `residue j`, then for every $j$ and every $i < n_j$ with $\mathrm{S.value}^{\texttt{layerTailDegree}\ m + 1} < $ `basisAxisScale (basis j) i` (where `layerTailDegree m` $= m(2^{m+1}+1)$), writing $h = $ `basisAxisScale (basis j) i` and $\mathrm{Mask}(z) = $ `allocatedIntegerKernelMask B U basis S x rows j modulus (residue j) z`:
--   - for every $z \in \mathbb{Z}^{O_j}$, $0 \le \mathrm{Mask}(z) \le$ `layerKernelIndexBound m M` $= M^{m\,2^{m+1}}$; and
--   - for every $v$ with $p(v) \ne 0$ and every $z \in \mathbb{Z}^{O_j}$,
--   $$\Bigl|h^{|O_j|}\,\texttt{allocatedIntegerKernelPMF}(\dots, v, \dots)(z) - \mathrm{Mask}(z)\cdot \texttt{allocatedIntegerKernelDensity B U basis S j i x u (rows j) (s j) (hA j)}\bigl(\hat v,\ (o \mapsto z_o / h)\bigr)\Bigr| \le \varepsilon,$$
--   where `allocatedIntegerKernelPMF B U basis hR hσ S x u v rows j i (hσ1 j) henormous` is OpenAI's probability mass function on $\mathbb{Z}^{O_j}$ (converted to a real number) and $\hat v$ = `principalTupleNormalized (principalAxisLength (fun a => ¬ grid a) sides) v` is $v$ with each entry divided by its side length.
--
--   Lean: `OAI.Erdos3.VectorPolynomial.allocatedFixedKernel_replacement_s2`, which states OpenAI's `OAI.Erdos3.VectorPolynomial.allocatedFixedKernel_replacement` (in `lean/OAI/Combinatorics/Progressions/Linear/AllocatedFixedKernelReplacement.lean`); the definitions it uses are in the definitions bundle `OAIE3v2B194` of version 2 of this split (and the bundles they import).
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/Progressions/Linear/AllocatedFixedKernelReplacement.lean (declaration OAI.Erdos3.VectorPolynomial.allocatedFixedKernel_replacement)

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIE3v2B194

section

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

theorem allocatedFixedKernel_replacement_s2 {M : ℕ} (hM : 0 < M)
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
    (hi : ∀ j : Fin m, fixedKernelInverseBound S.positive x (j.val+1) (rows j) (s j) (hA j) (1/(M : ℝ))) :
    ∀ (u : PrincipalAxisTuples (α := α) grid sides)
        (p : FiniteProbabilityWeights (PrincipalAxisTuples (α := α) (fun a => ¬grid a) sides))
        (residue : ∀ j, Matrix (O j) (AllocatedNonkernelCoefficient (G := G) B j) (ZMod modulus)),
      (∀ v, p.weight v ≠ 0 → ∀ j,
        integerResidueMatrix (allocatedNonkernelJetMatrix B U basis S x u rows j v) modulus = residue j) →
      ∀ j i (henormous : S.value^(layerTailDegree m+1) < basisAxisScale (basis j) i),
      (∀ z, 0 ≤ allocatedIntegerKernelMask B U basis S x rows j modulus (residue j) z ∧
        allocatedIntegerKernelMask B U basis S x rows j modulus (residue j) z ≤ layerKernelIndexBound m M) ∧
      ∀ v, p.weight v ≠ 0 → ∀ z,
        |(basisAxisScale (basis j) i : ℝ)^Fintype.card (O j) *
            (allocatedIntegerKernelPMF B U basis hR hσ S x u v rows j i (hσ1 j) henormous z).toReal -
          allocatedIntegerKernelMask B U basis S x rows j modulus (residue j) z *
            allocatedIntegerKernelDensity B U basis S j i x u (rows j) (s j) (hA j)
              (principalTupleNormalized (principalAxisLength (fun a => ¬grid a) sides) v)
              (fun o => (z o : ℝ)/(basisAxisScale (basis j) i : ℝ))| ≤ ε := by
  sorry

end Erdos3.VectorPolynomial

end

end OAI
end
