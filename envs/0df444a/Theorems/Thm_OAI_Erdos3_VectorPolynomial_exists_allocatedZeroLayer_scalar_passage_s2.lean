-- Prove2me | Theorems.Thm_OAI_Erdos3_VectorPolynomial_exists_allocatedZeroLayer_scalar_passage_s2
-- name    : OAI.Erdos3.VectorPolynomial.exists_allocatedZeroLayer_scalar_passage_s2
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-18T05:26:22.567699+00:00
-- url     : https://prove2.me/theorems/e6e1c835-3fe8-4f77-bdda-0444050f55a1
-- title:
--   A productive zero-layer external candidate problem with a patch-orbit conclusion yields a relative patch slice conclusion at a lowered target
-- statement:
--   Let $s, n_0, \mathrm{ratio}$ be natural numbers with $n_0 \ge 2$ and $\mathrm{ratio} \ge 2$, and let $\mathrm{discount}$ be a real number with $0 < \mathrm{discount} \le 1/2$. Then there are natural numbers $\mathrm{scalarE}, \mathrm{scalarC}, \mathrm{scalarF} \ge 2$ with the following property. All named objects below are defined by OpenAI, and all types are in the lowest universe `Type`.
--
--   Let $G, X$ be finite types. Take the layer count to be $m = 0$: let $I, E_{\mathrm{col}}, J$ be families of types indexed by $\operatorname{Fin} 0$ (so empty families), with $n$, $B$, $U$, $\mathrm{basis}$, $R$, $\sigma$, $S$ (a `LayerSamplerScale B U basis R σ`), $\mathrm{hb}$, $o$, $\mathrm{hR}$, $\mathrm{h\sigma}$ the corresponding (vacuous) data. Let $N : X \to \mathbb{N}$, $\mathrm{poly}$ and $\mathrm{hm}$ the (empty) family of polynomials with coefficients in $U$, $\sigma_{\mathrm{surplus}}$ a real number, and $\mathrm{center}$ a point of `CoefficientTorus U` (for variables `LayerSamplerVariables G I n B`); the lattice-section instances are assumed. Let $A$ be a proof of `AllocatedExternalCandidateSampler B U basis S hb o hR hσ N poly hm τ 1 (fun _ => 1) {0} center` with $\tau$ = `unconditionedSpatialTrimFraction (#X) σsurplus` $= \sigma_{\mathrm{surplus}} / (32(\#X + 1))$, narrowing $\xi = 1$, stride $1$ in every coordinate, and the single residue cell $0$ (a proposition stating: $N(x) > 0$ for all $x$, $\tau > 0$, $\xi > 0$, the strides are positive, the trimmed integer box `trimmedIntegerBox N (spatialTrimMargin τ N)` is nonempty, and two smooth/centered masses are positive). Assume (_hK) that the number of variables `LayerSamplerVariables G I n B` equals $n_0$. Let $V$ be a type, $d$ a natural number and `patch` a `PolynomialPatch V s d` (OpenAI's structure: monotone weights $1 \le w_i \le s$ for $i \in \operatorname{Fin} d$, polynomial slots, and a patch kernel), with a finite index type `PolynomialShearIndex patch.weight` and a topology on $\mathbb{R} \otimes_{\mathbb{Q}}$ `PolynomialShearLieAlgebra patch.weight ℚ` making it a Hausdorff topological vector space. Let $f : (X \to \mathbb{Z}) \to \mathbb{R}$ and $\lambda, \mathrm{cost}, \mathrm{massThreshold}, \mathrm{scoreThreshold}$ real numbers. Let $P$ be an `AllocatedExternalCandidateProblem` for $A$ (with column types $E_{\mathrm{col}}$), the nilmanifold `polynomialShearNilmanifold patch.weight s patch.weight_le`, the marked filtration `RationalTorus.trivialFiltration s` (on the zero Lie algebra), the zero Lie map, the marked orbit $1$, the observable $(x, y) \mapsto$ `patch.shearObservable y`, the weight $x \mapsto f(x) - \lambda$, and the thresholds $\mathrm{cost}, \mathrm{massThreshold}, \mathrm{scoreThreshold}$ (a set of productive sampler paths of mass at least massThreshold, each with a local chart and a candidate of score at least scoreThreshold). Assume (_hkeep) every productive path's chart keeps all coordinates. Let $\mathrm{outputCost}, \mathrm{outputMass}, \mathrm{outputScore}$ be reals and `out` a `P.Conclusion outputCost outputMass outputScore` (an ambient polynomial orbit `out.ambient` together with retained paths, dense residue box slices, and score bounds).
--
--   Let $b \ge 2$ be a real number and assume: $\#X \le b$; $0 < \sigma_{\mathrm{surplus}} \le 1$ and $\sigma_{\mathrm{surplus}}^{-1} \le e^b$; $\lambda \in [0, 1]$ and $e^{-b} \le \lambda$; $0 \le \mathrm{outputCost} \le b$; $e^{-b} \le \mathrm{outputMass}$; $e^{-b} \le \mathrm{outputScore}$; `relativePatchComplexity patch` $= d + \log(1 + \mathrm{lip})$ (lip the patch kernel's Lipschitz constant) is at most $b$. Let $g$ be a niltest on `polynomialShearNilmanifold patch.weight s patch.weight_le` with variables $X$ (all of weight $1$) of complexity at most $b$, such that $g.\mathrm{eval}(x)$ equals the value of the patch `patch.ofZeroLayerShearOrbit out.ambient` at the real point $(x_i)_i$ for every $x : X \to \mathbb{Z}$. Put $p = (b+2)^{\mathrm{scalarE}}$, $\mathrm{target} = 8\,(\mathrm{ratio} \cdot n_0 + 1)(p+1)$ and $\mathrm{budget} = (\mathrm{target} + 2)^{\mathrm{scalarC}}$. Assume $e^{\mathrm{budget}} \le$ `A.sides i` $\le \mathrm{ratio} \cdot e^{\mathrm{budget}}$ for every variable $i$ (here `A.sides` $i$ is `S.value` for $i \in G$), $e^{(p + \mathrm{scalarF})^{\mathrm{scalarF}}} \le N(i)$ for every $i \in X$, and $f(x) \in [0,1]$ for every $x$ in `integerBox N` $= \prod_i ([0, N(i)) \cap \mathbb{Z})$. Then `RelativePatchSliceConclusion s N f ((1 - discount) λ) d ((p + scalarF)^scalarF)` holds; that is, with $c = (p + \mathrm{scalarF})^{\mathrm{scalarF}}$, there are a positive natural number $q$, a residue box slice $S'$ of `integerBox N` with step $q$, a natural number $d' \le d$ and a `PolynomialPatch X s d'` $A'$ such that every side length of $S'$ is at least $e^{-c} N(i)$, `relativePatchComplexity A'` $\le c$, and $e^{-c} \le$ `relativePatchSliceScore S' f ((1 - discount) λ) A'` (the average over the slice points of $(f - (1-\mathrm{discount})\lambda)$ times the patch value at the slice coordinates).
--
--   Lean: `OAI.Erdos3.VectorPolynomial.exists_allocatedZeroLayer_scalar_passage_s2`, which states OpenAI's `OAI.Erdos3.VectorPolynomial.exists_allocatedZeroLayer_scalar_passage` (in `lean/OAI/Combinatorics/Progressions/Estimates/AllocatedZeroLayerScalarPassage.lean`); the definitions it uses are in the definitions bundles `OAIE3v2B148`, `OAIE3v2B237` of version 2 of this split (and the bundles they import).
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/Progressions/Estimates/AllocatedZeroLayerScalarPassage.lean (declaration OAI.Erdos3.VectorPolynomial.exists_allocatedZeroLayer_scalar_passage)

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIE3v2B148
import Definitions.Def_OAIE3v2B237

section

namespace OAI

section

namespace Erdos3.VectorPolynomial

open Module Submodule BooleanCubeKernel NilpotentLieFiltration NilpotentLieBCHGroup
open scoped BigOperators Classical TensorProduct NNReal

attribute [local irreducible] selectedJointReference trimmedIntegerBox
  trimmedSpatialWidths spatialTrimMargin rectangularWeightIndices
  unconditionedSpatialTrimFraction selectedResidueSmoothWeight

theorem exists_allocatedZeroLayer_scalar_passage_s2 (s n₀ ratio : ℕ)
    (hn₀ : 2 ≤ n₀) (hratio : 2 ≤ ratio)
    {discount : ℝ} (hdiscount : 0 < discount) (hdiscountHalf : discount ≤ 1 / 2) :
    ∃ scalarE scalarC scalarF : ℕ,
      2 ≤ scalarE ∧ 2 ≤ scalarC ∧ 2 ≤ scalarF ∧
    ∀ {G X : Type} [Fintype G] [Fintype X]
      {I Ecol J : Fin 0 → Type} [∀ j, Fintype (I j)] [∀ j, Fintype (J j)]
      {n : Fin 0 → ℕ} {B : LayerSamplerAxis I n → Type} [∀ a, Fintype (B a)]
      {U : ∀ j, Submodule ℝ (J j → ℝ)}
      {basis : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ}
      {R σ : Fin 0 → ℝ} {S : LayerSamplerScale (G := G) B U basis R σ}
      {hb : ∀ j, span ℤ (Set.range (basis j)) = projectedIntegerLattice (euclideanSubspace (U j))}
      {o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j))}
      {hR : ∀ j, 0 < R j} {hσ : ∀ j, 0 < σ j}
      {N : X → ℕ} {poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ)}
      {hm : ∀ j e, coefficients (poly j) e ∈ U j}
      {σsurplus : ℝ}
      {center : CoefficientTorus (K := LayerSamplerVariables G I n B) U}
      [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]
      (A : AllocatedExternalCandidateSampler B U basis S hb o hR hσ N poly hm
        (unconditionedSpatialTrimFraction (Fintype.card X) σsurplus) 1
        (fun _ : X => 1) {0} center)
      (_hK : Fintype.card (LayerSamplerVariables G I n B) = n₀)
      {V : Type} {d : ℕ} (patch : PolynomialPatch V s d)
      [Fintype (PolynomialShearIndex patch.weight)]
      [TopologicalSpace (ℝ ⊗[ℚ] PolynomialShearLieAlgebra patch.weight ℚ)]
      [IsTopologicalAddGroup (ℝ ⊗[ℚ] PolynomialShearLieAlgebra patch.weight ℚ)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] PolynomialShearLieAlgebra patch.weight ℚ)]
      [T2Space (ℝ ⊗[ℚ] PolynomialShearLieAlgebra patch.weight ℚ)]
      {f : (X → ℤ) → ℝ} {lam cost massThreshold scoreThreshold : ℝ}
      (P : AllocatedExternalCandidateProblem (E := Ecol) A
        (polynomialShearNilmanifold patch.weight s patch.weight_le)
        (RationalTorus.trivialFiltration s) 0 1
        (fun _ y => (patch.shearObservable y : ℂ))
        (fun x => ((f x - lam : ℝ) : ℂ)) cost massThreshold scoreThreshold)
      (_hkeep : ∀ z : P.productive, (P.chart z).keep = (fun _ => True))
      {outputCost outputMass outputScore : ℝ}
      (out : P.Conclusion outputCost outputMass outputScore)
      (b : ℝ), 2 ≤ b → (Fintype.card X : ℝ) ≤ b →
      0 < σsurplus → σsurplus ≤ 1 → σsurplus⁻¹ ≤ Real.exp b →
      lam ∈ Set.Icc (0 : ℝ) 1 → Real.exp (-b) ≤ lam →
      0 ≤ outputCost → outputCost ≤ b →
      Real.exp (-b) ≤ outputMass → Real.exp (-b) ≤ outputScore →
      relativePatchComplexity patch ≤ b →
      ∀ g : (polynomialShearNilmanifold patch.weight s patch.weight_le).Niltest
        (fun _ : X => 1), g.ComplexityLE b →
      (∀ x : X → ℤ, g.eval x =
        ((patch.ofZeroLayerShearOrbit out.ambient).value (fun i => (x i : ℝ)) : ℂ)) →
      let p := (b + 2) ^ scalarE
      let target := 8 * ((ratio * n₀ : ℕ) + 1 : ℝ) * (p + 1)
      let budget := (target + 2) ^ scalarC
      (∀ i, Real.exp budget ≤ (A.sides i : ℝ)) →
      (∀ i, (A.sides i : ℝ) ≤ (ratio : ℝ) * Real.exp budget) →
      (∀ i, Real.exp ((p + scalarF) ^ scalarF) ≤ (N i : ℝ)) →
      (∀ x ∈ integerBox N, f x ∈ Set.Icc (0 : ℝ) 1) →
      RelativePatchSliceConclusion s N f ((1 - discount) * lam) d
        ((p + scalarF) ^ scalarF) := by
  sorry

end Erdos3.VectorPolynomial

end

end OAI
end
