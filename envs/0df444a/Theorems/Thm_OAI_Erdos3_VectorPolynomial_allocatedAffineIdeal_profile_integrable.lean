-- Prove2me | Theorems.Thm_OAI_Erdos3_VectorPolynomial_allocatedAffineIdeal_profile_integrable
-- name    : OAI.Erdos3.VectorPolynomial.allocatedAffineIdeal_profile_integrable
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-09T23:36:01.611009+00:00
-- url     : https://prove2.me/theorems/7083b6a5-b602-4c27-9e93-1a4f53d0fce0
-- title:
--   The long profile density of the affine ideal is integrable against the long-jet reference
-- statement:
--   Fix the section data: a natural number $m$; finite types $G$ and $I_j$, natural numbers $n_j$, finite types $B_a$ over the axes $a$ of `LayerSamplerAxis I n`; finite types $J_j$, real subspaces $U_j \subseteq \mathbb R^{J_j}$ and bases `basis j` (indexed by $\mathrm{Fin}\,n_j$) of the orthogonal complements of `euclideanSubspace (U j)`; real functions $R, \sigma$ on $\mathrm{Fin}\,m$ with $R_j > 0$ for all $j$ (hypothesis $hR$); a layer-sampler scale `S : LayerSamplerScale B U basis R σ`; a finite type $\alpha$ with decidable equality and a point $x : G \to $ `IntegerScalarCubeBox α S.value`; finite types $O_j$ and maps $\mathrm{rows}_j : O_j \to \mathrm{Finset}\,\alpha$. Let grid be the predicate `allocatedGridAxis U basis S.value` on axes, input the type `PrincipalAxisParameter (¬ grid)` (a parameter type defined by OpenAI over the non-grid axes), and output $= \Sigma_{a\ \text{non-grid}}\, O_{\mathrm{layer}(a)}$. Let $P$ be real with $R_j \le e^P$ and $R_j^{-1} \le e^P$ for all $j$; let $\rho \in \mathbb R_{\ge 0}$ with $0 < \rho \le 1$; let $\mathrm{center}, \mathrm{width} : \mathrm{input} \to \mathbb R$ with $|\mathrm{center}(i)| + |\mathrm{width}(i)| \le 1$ for all $i$; let $\mathrm{modulus}$ be a natural number and, for each $j$, $\mathrm{residue}_j$ a matrix over $\mathbb Z/\mathrm{modulus}$ with rows $O_j$ and columns `AllocatedNonkernelCoefficient B j`; and let $C_{\mathrm{mask}} \ge 1$ be real with $0 \le$ `allocatedIntegerKernelMask B U basis S x rows j modulus (residue j) z` $\le C_{\mathrm{mask}}$ for all $j, z$. Then the function `allocatedLongProfileDensity B U basis S x rows modulus residue g` is integrable with respect to the measure `allocatedLongJetReference B U basis S O`, where $g = $ `diagonalImageDensity (o ↦ R_{layer(o)}) (activeAveragedSlicedProfileIdeal (G × Option α) (layerSamplerDegree I n) grid rows ρ center width)`; here `diagonalImageDensity d f` is $y \mapsto (\prod_i |d_i|)^{-1} f(i \mapsto y_i/d_i)$ and `activeAveragedSlicedProfileIdeal` is a real function defined by OpenAI.
--
--   Lean: `OAI.Erdos3.VectorPolynomial.allocatedAffineIdeal_profile_integrable` in `lean/OAI/Combinatorics/Progressions/Lattices/AllocatedAffineProfileMeanTransport.lean` (OpenAI); the definitions it uses are in the definitions bundles `OAIErdos3B176` of this split (and the bundles they import).
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/Progressions/Lattices/AllocatedAffineProfileMeanTransport.lean#L58

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIErdos3B176

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

include hR in
 theorem allocatedAffineIdeal_profile_integrable
    {P : ℝ} (hRP : ∀ j, R j ≤ Real.exp P) (hRi : ∀ j, (R j)⁻¹ ≤ Real.exp P)
    (ρ : ℝ≥0) (hρ : 0 < ρ) (hρone : ρ ≤ 1)
    (center width : input → ℝ) (hw : ∀ i, |center i| + |width i| ≤ 1)
    (modulus : ℕ)
    (residue : ∀ j, Matrix (O j) (AllocatedNonkernelCoefficient (G := G) B j) (ZMod modulus))
    {Cmask : ℝ} (hCmask : 1 ≤ Cmask)
    (hmask : ∀ j z, 0 ≤ allocatedIntegerKernelMask B U basis S x rows j modulus (residue j) z ∧
      allocatedIntegerKernelMask B U basis S x rows j modulus (residue j) z ≤ Cmask) :
    Integrable (allocatedLongProfileDensity B U basis S x rows modulus residue
      (diagonalImageDensity (fun o : output => R o.1.val.1)
        (activeAveragedSlicedProfileIdeal (G := G) (B := B) (G × Option α)
          (layerSamplerDegree I n) grid (fun a => rows a.val.1) ρ center width)))
      (allocatedLongJetReference B U basis S O) := by
  sorry

end Erdos3.VectorPolynomial
end
end OAI
