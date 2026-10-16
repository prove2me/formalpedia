-- Prove2me | Theorems.Thm_OAI_Erdos3_VectorPolynomial_exists_allocatedZeroLayer_degree_scalar_conclusion
-- name    : OAI.Erdos3.VectorPolynomial.exists_allocatedZeroLayer_degree_scalar_conclusion
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-10-16T01:45:02.284369+00:00
-- url     : https://prove2.me/theorems/45a8374a-f30a-4142-a5b3-ce2022a43773
-- title:
--   A zero-layer candidate problem with degree globalization gives a relative slice
-- statement:
--   Let $s, n_0, \mathrm{ratio}$ be natural numbers with $n_0 \ge 2$ and $\mathrm{ratio} \ge 2$, and let $\mathrm{discount}$ be real with $0 < \mathrm{discount} \le 1/2$. Then there exist natural numbers $C_{\mathrm{obs}}, C_{\mathrm{nat}}, E, C, F$ (`observableC`, `nativeC`, `scalarE`, `scalarC`, `scalarF`), each at least $2$, with the following property.
--
--   Let $G, X$ be finite types; take zero layers, i.e. families $I, E_{\mathrm{col}}, J$ of types and $n$ indexed by $\mathrm{Fin}\,0$, types $B_a$ over `LayerSamplerAxis I n`, subspaces $U_j$, bases $\mathrm{basis}_j$, $R, \sigma : \mathrm{Fin}\,0 \to \mathbb R$, proofs $hb$, $hR$, $h\sigma$, orthonormal bases $o_j$, vector polynomials $\mathrm{poly}_j$ with coefficients in $U_j$ (proof $hm$) and `IsZLattice` instances (vacuous families since $\mathrm{Fin}\,0$ is empty); let $S$ be a `LayerSamplerScale` for $(B, U, \mathrm{basis}, R, \sigma)$ over $G$ (a structure bundling a positive natural number $S.\mathrm{value}$ with width and gap inequalities), $N : X \to \mathbb N$, $\sigma_{\mathrm{surplus}}$ real, and `center` a point of the `CoefficientTorus U`. Let $A$ be a proof of `AllocatedExternalCandidateSampler B U basis S hb o hR hσ N poly hm τ 1 (fun _ => 1) {0} center` with $\tau =$ `unconditionedSpatialTrimFraction |X| σsurplus` $= \sigma_{\mathrm{surplus}}/(32(|X|+1))$ (a proposition bundling positivity conditions and positive masses), and assume $|$`LayerSamplerVariables G I n B`$| = n_0$. Let $V$ be a type, $d$ a natural number and `patch` a `PolynomialPatch V s d` (weights in $[1,s]$, slot centers `patch.form.center i`, and a kernel with Lipschitz constant `patch.kernel.lip`), with a `Fintype` instance on `PolynomialShearIndex patch.weight` and a topology on $\mathbb R \otimes_{\mathbb Q}$ `PolynomialShearLieAlgebra patch.weight ℚ` making it a Hausdorff topological vector space. Let $f : (X \to \mathbb Z) \to \mathbb R$ and reals $\lambda$, $\mathrm{cost}$, $\mathrm{massThreshold}$, $\mathrm{scoreThreshold}$; let $P$ be an `AllocatedExternalCandidateProblem` for $A$, the nilmanifold `polynomialShearNilmanifold patch.weight s _`, the filtration `RationalTorus.trivialFiltration s`, the parameters $0$ and $1$, the observable $(\_, y) \mapsto$ `patch.shearObservable y`, the weight $x \mapsto f(x) - \lambda$, and these cost and thresholds (a structure bundling a finite set `P.productive` of paths, local charts `P.chart z` and candidates with scores), such that `(P.chart z).keep` is the always-true predicate for every productive $z$. Let $p_{\mathrm{patch}}, p_{\mathrm{global}}, \mathrm{outputCost}, b$ be reals and $\mathrm{netExponent}$ a natural number. Assume, in order: $0 \le p_{\mathrm{patch}}$; $d \le p_{\mathrm{patch}}$; `realPolynomialMass (patch.form.center i)` $\le p_{\mathrm{patch}}$ for all $i$ (the sum of absolute values of the coefficients); `patch.kernel.lip` $\le e^{p_{\mathrm{patch}}}$; $(p_{\mathrm{patch}} + 2)^{C_{\mathrm{obs}}} \le p_{\mathrm{global}}$; $(p_{\mathrm{patch}} + 2)^{C_{\mathrm{nat}}} \le b$; $0 \le p_{\mathrm{global}}$; $\mathrm{cost} \le p_{\mathrm{global}}$; $e^{-p_{\mathrm{global}}} \le \mathrm{massThreshold}$; $e^{-p_{\mathrm{global}}} \le \mathrm{scoreThreshold}$; $b \ge 2$; $|X| \le b$; $0 < \sigma_{\mathrm{surplus}} \le 1$; $\sigma_{\mathrm{surplus}}^{-1} \le e^b$; $\lambda \in [0,1]$; $e^{-b} \le \lambda$; $0 \le \mathrm{outputCost} \le b$; $f(x) \in [0,1]$ for all $x$; and `A.DegreeGlobalizationAt (x ↦ f x - λ) s netExponent pGlobal outputCost` (a proposition of OpenAI: for all rational filtered nilmanifolds of degree $s$ and complexity at most $p_{\mathrm{global}}$ related by a filtered Lie map, all bounded Lipschitz $[0,1]$-valued observables admitting small nets, and every candidate problem with cost $p_{\mathrm{global}}$ and thresholds $e^{-p_{\mathrm{global}}}$ for the weight $x \mapsto f(x) - \lambda$, the problem's `Conclusion` with cost $\mathrm{outputCost}$ and thresholds $e^{-\mathrm{outputCost}}$ is nonempty). Put $p = (b+2)^E$, $\mathrm{target} = 8(\mathrm{ratio} \cdot n_0 + 1)(p+1)$ and $\mathrm{budget} = (\mathrm{target} + 2)^C$. Assume further $e^{\mathrm{budget}} \le$ `A.sides i` $\le \mathrm{ratio} \cdot e^{\mathrm{budget}}$ for all $i$, and $\exp((p + F)^F) \le N_i$ for all $i$.
--
--   Then `RelativePatchSliceConclusion s N f ((1 - discount) λ) d ((p + F)^F)` holds: there exist $q > 0$, a `ResidueBoxSlice N q` $S'$, a natural number $d'$ and a `PolynomialPatch X s d'` $A'$ such that every side length of $S'$ is at least $\exp(-(p+F)^F) N_i$, $d' \le d$, `relativePatchComplexity A'` $\le (p+F)^F$, and $\exp(-(p+F)^F) \le$ `relativePatchSliceScore S' f ((1 - discount) λ) A'`.
--
--   Lean: `OAI.Erdos3.VectorPolynomial.exists_allocatedZeroLayer_degree_scalar_conclusion` in `lean/OAI/Combinatorics/Progressions/Polynomial/AllocatedZeroLayerDegreeScalarConclusion.lean` (OpenAI); the definitions it uses are in the definitions bundles `OAIErdos3B1342` of this split (and the bundles they import).
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/Progressions/Polynomial/AllocatedZeroLayerDegreeScalarConclusion.lean#L496

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIErdos3B1342

namespace OAI

section

namespace Erdos3

open scoped NNReal TensorProduct Classical

namespace PolynomialPatch

variable {V : Type*} {s d : ℕ} (P : PolynomialPatch V s d)
  [Fintype (PolynomialShearIndex P.weight)]
  [TopologicalSpace (ℝ ⊗[ℚ] PolynomialShearLieAlgebra P.weight ℚ)]
  [IsTopologicalAddGroup (ℝ ⊗[ℚ] PolynomialShearLieAlgebra P.weight ℚ)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] PolynomialShearLieAlgebra P.weight ℚ)]
  [T2Space (ℝ ⊗[ℚ] PolynomialShearLieAlgebra P.weight ℚ)]

end PolynomialPatch

end Erdos3

end

section

namespace Erdos3.VectorPolynomial
open Module Submodule BooleanCubeKernel NilpotentLieFiltration NilpotentLieBCHGroup
open scoped BigOperators Classical TensorProduct NNReal

variable {m : ℕ} {G X : Type*} [Fintype G] [Fintype X]
    {I E J : Fin m → Type*} [∀ j, Fintype (I j)] [∀ j, Fintype (J j)]
    {n : Fin m → ℕ} {B : LayerSamplerAxis I n → Type*} [∀ a, Fintype (B a)]
    {U : ∀ j, Submodule ℝ (J j → ℝ)}
    {b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ}
    {R σ : Fin m → ℝ} {S : LayerSamplerScale (G := G) B U b R σ}
    {hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j))}
    {o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j))}
    {hR : ∀ j, 0 < R j} {hσ : ∀ j, 0 < σ j}
    {N : X → ℕ} {poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ)}
    {hm : ∀ j e, coefficients (poly j) e ∈ U j}
    {τ ξ : ℝ} {stride : X → ℕ}
    {cells : Finset (ColumnResiduePattern (Option (LayerSamplerVariables G I n B)) X stride)}
    {center : CoefficientTorus (K := LayerSamplerVariables G I n B) U}
    [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]
    (A : AllocatedExternalCandidateSampler B U b S hb o hR hσ N poly hm τ ξ stride cells center)

namespace AllocatedExternalCandidateSampler

end AllocatedExternalCandidateSampler
end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open Module Submodule BooleanCubeKernel NilpotentLieFiltration NilpotentLieBCHGroup
open scoped BigOperators Classical TensorProduct NNReal

variable {m : ℕ} {G X : Type*} [Fintype G] [Fintype X]
    {I E J : Fin m → Type*} [∀ j, Fintype (I j)] [∀ j, Fintype (J j)]
    {n : Fin m → ℕ} {B : LayerSamplerAxis I n → Type*} [∀ a, Fintype (B a)]
    {U : ∀ j, Submodule ℝ (J j → ℝ)}
    {b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ}
    {R σ : Fin m → ℝ} {S : LayerSamplerScale (G := G) B U b R σ}
    {hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j))}
    {o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j))}
    {hR : ∀ j, 0 < R j} {hσ : ∀ j, 0 < σ j}
    {N : X → ℕ} {poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ)}
    {hm : ∀ j e, coefficients (poly j) e ∈ U j}
    {τ ξ : ℝ} {stride : X → ℕ}
    {cells : Finset (ColumnResiduePattern (Option (LayerSamplerVariables G I n B)) X stride)}
    {center : CoefficientTorus (K := LayerSamplerVariables G I n B) U}
    [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]
    (A : AllocatedExternalCandidateSampler B U b S hb o hR hσ N poly hm τ ξ stride cells center)

namespace AllocatedExternalCandidateSampler

end AllocatedExternalCandidateSampler
end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open Module Submodule BooleanCubeKernel NilpotentLieFiltration NilpotentLieBCHGroup
open scoped BigOperators Classical TensorProduct NNReal

variable {m : ℕ} {G X : Type} [Fintype G] [Fintype X]
    {I E J : Fin m → Type} [∀ j, Fintype (I j)] [∀ j, Fintype (J j)]
    {n : Fin m → ℕ} {B : LayerSamplerAxis I n → Type} [∀ a, Fintype (B a)]
    {U : ∀ j, Submodule ℝ (J j → ℝ)}
    {b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ}
    {R σ : Fin m → ℝ} {S : LayerSamplerScale (G := G) B U b R σ}
    {hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j))}
    {o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j))}
    {hR : ∀ j, 0 < R j} {hσ : ∀ j, 0 < σ j}
    {N : X → ℕ} {poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ)}
    {hm : ∀ j e, coefficients (poly j) e ∈ U j}
    {τ ξ : ℝ} {stride : X → ℕ}
    {cells : Finset (ColumnResiduePattern (Option (LayerSamplerVariables G I n B)) X stride)}
    {center : CoefficientTorus (K := LayerSamplerVariables G I n B) U}
    [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]
    {A : AllocatedExternalCandidateSampler B U b S hb o hR hσ N poly hm τ ξ stride cells center}

namespace AllocatedExternalCandidateProblem

variable {V : Type*} {s d : ℕ} (patch : PolynomialPatch V s d)
    [Fintype (PolynomialShearIndex patch.weight)]
    [TopologicalSpace (ℝ ⊗[ℚ] PolynomialShearLieAlgebra patch.weight ℚ)]
    [IsTopologicalAddGroup (ℝ ⊗[ℚ] PolynomialShearLieAlgebra patch.weight ℚ)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] PolynomialShearLieAlgebra patch.weight ℚ)]
    [T2Space (ℝ ⊗[ℚ] PolynomialShearLieAlgebra patch.weight ℚ)]
    {f : (X → ℤ) → ℝ} {lam cost mass score : ℝ}
    (P : AllocatedExternalCandidateProblem (E := E) A
      (polynomialShearNilmanifold patch.weight s patch.weight_le)
      (RationalTorus.trivialFiltration s) 0 1
      (fun _ y => (patch.shearObservable y : ℂ))
      (fun x => ((f x - lam : ℝ) : ℂ)) cost mass score)

end AllocatedExternalCandidateProblem
end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open Module Submodule BooleanCubeKernel NilpotentLieFiltration NilpotentLieBCHGroup
open scoped BigOperators Classical TensorProduct NNReal

variable {m : ℕ} {G X : Type} [Fintype G] [Fintype X]
    {I E J : Fin m → Type} [∀ j, Fintype (I j)] [∀ j, Fintype (J j)]
    {n : Fin m → ℕ} {B : LayerSamplerAxis I n → Type} [∀ a, Fintype (B a)]
    {U : ∀ j, Submodule ℝ (J j → ℝ)}
    {b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ}
    {R σ : Fin m → ℝ} {S : LayerSamplerScale (G := G) B U b R σ}
    {hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j))}
    {o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j))}
    {hR : ∀ j, 0 < R j} {hσ : ∀ j, 0 < σ j}
    {N : X → ℕ} {poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ)}
    {hm : ∀ j e, coefficients (poly j) e ∈ U j}
    {τ ξ : ℝ} {stride : X → ℕ}
    {cells : Finset (ColumnResiduePattern (Option (LayerSamplerVariables G I n B)) X stride)}
    {center : CoefficientTorus (K := LayerSamplerVariables G I n B) U}
    [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]
    {A : AllocatedExternalCandidateSampler B U b S hb o hR hσ N poly hm τ ξ stride cells center}

namespace AllocatedExternalCandidateProblem

variable {V : Type} {s d : ℕ} (patch : PolynomialPatch V s d)
    [Fintype (PolynomialShearIndex patch.weight)]
    {f : (X → ℤ) → ℝ} {target cost childCost normBudget : ℝ}
    {rankBound : ℕ} {productive : Finset A.Path}
    (P : AllocatedExternalCandidateProblem (E := E) A
      (polynomialShearNilmanifold patch.weight s patch.weight_le)
      (RationalTorus.trivialFiltration s) 0 1
      (fun _ y => (patch.shearObservable y : ℂ))
      (fun x => ((f x - target : ℝ) : ℂ)) cost
      ((A.law.mass productive /
        ((min rankBound ⌊childCost⌋₊ + 1) * (s + 1) ^ min rankBound ⌊childCost⌋₊ : ℕ)) *
        Real.exp (-normBudget)) (Real.exp (-normBudget)))

end AllocatedExternalCandidateProblem

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open Module Submodule BooleanCubeKernel NilpotentLieFiltration NilpotentLieBCHGroup
open scoped BigOperators Classical TensorProduct NNReal

theorem exists_allocatedZeroLayer_degree_scalar_conclusion (s n₀ ratio : ℕ)
    (hn₀ : 2 ≤ n₀) (hratio : 2 ≤ ratio)
    {discount : ℝ} (hdiscount : 0 < discount) (hdiscountHalf : discount ≤ 1 / 2) :
    ∃ observableC nativeC scalarE scalarC scalarF : ℕ,
      2 ≤ observableC ∧ 2 ≤ nativeC ∧
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
      (pPatch pGlobal outputCost b : ℝ) (netExponent : ℕ),
      0 ≤ pPatch → (d : ℝ) ≤ pPatch →
      (∀ i, realPolynomialMass (patch.form.center i) ≤ pPatch) →
      (patch.kernel.lip : ℝ) ≤ Real.exp pPatch →
      (pPatch + 2) ^ observableC ≤ pGlobal →
      (pPatch + 2) ^ nativeC ≤ b →
      0 ≤ pGlobal → cost ≤ pGlobal →
      Real.exp (-pGlobal) ≤ massThreshold → Real.exp (-pGlobal) ≤ scoreThreshold →
      2 ≤ b → (Fintype.card X : ℝ) ≤ b →
      0 < σsurplus → σsurplus ≤ 1 → σsurplus⁻¹ ≤ Real.exp b →
      lam ∈ Set.Icc (0 : ℝ) 1 → Real.exp (-b) ≤ lam →
      0 ≤ outputCost → outputCost ≤ b →
      (∀ x, f x ∈ Set.Icc (0 : ℝ) 1) →
      A.DegreeGlobalizationAt (E := Ecol) (fun x => ((f x - lam : ℝ) : ℂ))
        s netExponent pGlobal outputCost →
      let p := (b + 2) ^ scalarE
      let target := 8 * ((ratio * n₀ : ℕ) + 1 : ℝ) * (p + 1)
      let budget := (target + 2) ^ scalarC
      (∀ i, Real.exp budget ≤ (A.sides i : ℝ)) →
      (∀ i, (A.sides i : ℝ) ≤ (ratio : ℝ) * Real.exp budget) →
      (∀ i, Real.exp ((p + scalarF) ^ scalarF) ≤ (N i : ℝ)) →
      RelativePatchSliceConclusion s N f ((1 - discount) * lam) d
        ((p + scalarF) ^ scalarF) := by
  sorry

end Erdos3.VectorPolynomial
end
end OAI
