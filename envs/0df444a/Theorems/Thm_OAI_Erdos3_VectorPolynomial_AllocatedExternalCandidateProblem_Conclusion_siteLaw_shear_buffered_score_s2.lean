-- Prove2me | Theorems.Thm_OAI_Erdos3_VectorPolynomial_AllocatedExternalCandidateProblem_Conclusion_siteLaw_shear_buffered_score_s2
-- name    : OAI.Erdos3.VectorPolynomial.AllocatedExternalCandidateProblem.Conclusion.siteLaw_shear_buffered_score_s2
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-18T06:59:38.996982+00:00
-- url     : https://prove2.me/theorems/1c850c42-d193-418e-af75-02fd0cc53b9d
-- title:
--   A candidate conclusion's score is bounded by a buffered shear score under its site law
-- statement:
--   Work in OpenAI's layer-sampler setting, with the following implicit: a natural number $m$; finite types $G$, $X$, $I_j$, $J_j$, types $E_j$, natural numbers $n_j$ and finite types $B_a$; subspaces $U_j\subseteq\mathbb{R}^{J_j}$ and bases $b_j$ of the orthogonal complements of `euclideanSubspace (U j)`; reals $R_j>0$, $\sigma_j>0$ (proofs $hR$, $h\sigma$) and a `LayerSamplerScale` $S$; $hb$ (the $\mathbb{Z}$-span of the range of $b_j$ is `projectedIntegerLattice (euclideanSubspace (U j))`); orthonormal bases $o_j$ of `euclideanSubspace (U j)`; $N:X\to\mathbb{N}$; vector polynomials $\mathrm{poly}_j$ on $X$ with values in $\mathbb{R}^{J_j}$ and coefficients in $U_j$ ($hm$); reals $\tau,\xi$; $\mathrm{stride}:X\to\mathbb{N}$; a finset $\mathrm{cells}$ of `ColumnResiduePattern`s; a point $\mathrm{center}$ of `CoefficientTorus U`; with each `latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))` a $\mathbb{Z}$-lattice. Let $A$ be an `AllocatedExternalCandidateSampler B U b S hb o hR hσ N poly hm τ ξ stride cells center` (implicit; a proposition bundling positivity facts for the sampler, whose path and site types and law OpenAI defines from these data). Further implicit: types $Y$ and $M$ with $M$ a Lie algebra over $\mathbb{Q}$, natural numbers $s,d,t$, a `NilpotentLieFiltration M t` $F_{\mathrm{mark}}$, a Lie algebra map $\varphi$ from `PolynomialShearLieAlgebra patch.weight ℚ` to $M$, a polynomial orbit $\mathrm{marked}$, reals $\mathrm{cost},\mathrm{massThreshold},\mathrm{scoreThreshold},\mathrm{outputCost},\mathrm{outputMass},\mathrm{outputScore}$, and an `AllocatedExternalCandidateProblem A (polynomialShearNilmanifold patch.weight s patch.weight_le) Fmark φ marked (fun _ z => patch.shearObservable z) (fun x => f x - lam) cost massThreshold scoreThreshold` named $P$ (a structure bundling a productive set of paths of mass at least $\mathrm{massThreshold}$, local charts, a center lift $P.\mathrm{centerLift}_j\in U_j$, and local candidates of score at least $\mathrm{scoreThreshold}$). Explicit: a `PolynomialPatch Y s d` named $\mathrm{patch}$ (with a `Fintype` instance on `PolynomialShearIndex patch.weight`), a function $f:\mathbb{Z}^X\to\mathbb{R}$, a real $\lambda$, and $\mathrm{out}$, a `P.Conclusion outputCost outputMass outputScore` (a structure bundling an ambient polynomial orbit $\mathrm{out.ambient}$, a retained finset of paths of mass at least $\mathrm{outputMass}$, and for each retained path a dense residue box slice with score at least $\mathrm{outputScore}$). Assume $\sigma_j\le1$; let $H_j\ge0$ with $\|\Phi_j^{-1}v\|\le H_j\|v\|$, where $\Phi_j$ is `normalizedOrthogonalChart (euclideanSubspace (U j)) (b j)`, and $H_j\,(|I_j|+1)\,R_j\le1/8$ for all $j$; assume $\mathrm{poly}_j$ has degree at most $j+1$ (`DegreeLE 1 (j+1)`). Let $\mathrm{tagCount}$ be a natural number, $e:\mathrm{Fin}\,\mathrm{tagCount}\simeq\Sigma_j J_j$, and $z$ a retained path of $\mathrm{out}$. Then
--   $$\mathrm{outputScore}\le\mathbb{E}_{\mathrm{site}\sim\mathrm{out.siteLaw}(z)}\ \text{bufferedScalarScore}\big(\chi,\ \mathrm{coord},\ T,\ f,\ \lambda,\ A.\mathrm{physical}(z,\mathrm{site})\big),$$
--   where $\chi$ = `majorPhasePlateauKernel tagCount` (the kernel $x\mapsto$ `linearCutoff (1/8) (1/8) ‖x‖`), $\mathrm{coord}$ = `fullTaggedBufferedCoordinates e poly (fun j => (P.centerLift j).val)` (the map $x\mapsto(i\mapsto\mathrm{poly}_{e(i).1}(x)_{e(i).2}-\mathrm{centerLift}_{e(i).1,e(i).2})$), $T(x,\ell)$ is the value of `patch.ofTaggedWeightedShearOrbit e out.ambient` at the point $(x,\ell)$ of $\mathbb{R}^{X}\times\mathbb{R}^{\mathrm{tagCount}}$, and `bufferedScalarScore χ x T f λ u` $=(f(u)-\lambda)\,\chi(x(u)-[x(u)])\,T(u,[x(u)])$ with $[\cdot]$ the nearest integer lift (`nearestIntegerLift`); $A.\mathrm{physical}(z,\mathrm{site})\in\mathbb{Z}^X$ is the physical point (`jointIntegerPhysicalSite`) of the site along the path.
--
--   Lean: `OAI.Erdos3.VectorPolynomial.AllocatedExternalCandidateProblem.Conclusion.siteLaw_shear_buffered_score_s2`, which states OpenAI's `OAI.Erdos3.VectorPolynomial.AllocatedExternalCandidateProblem.Conclusion.siteLaw_shear_buffered_score` (in `lean/OAI/Combinatorics/Progressions/Sampling/AllocatedExternalCandidateShearBufferedScore.lean`); the definitions it uses are in the definitions bundles `OAIE3v2B262`, `OAIE3v2B264` of version 2 of this split (and the bundles they import).
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/Progressions/Sampling/AllocatedExternalCandidateShearBufferedScore.lean (declaration OAI.Erdos3.VectorPolynomial.AllocatedExternalCandidateProblem.Conclusion.siteLaw_shear_buffered_score)

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIE3v2B262
import Definitions.Def_OAIE3v2B264

section

namespace OAI

section

namespace Erdos3.VectorPolynomial

open Module Submodule BooleanCubeKernel NilpotentLieFiltration NilpotentLieBCHGroup
open scoped BigOperators Classical TensorProduct

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

namespace AllocatedExternalCandidateProblem.Conclusion

variable {A} {Y M : Type*} [LieRing M] [LieAlgebra ℚ M] {s d t : ℕ}
    (patch : PolynomialPatch Y s d) [Fintype (PolynomialShearIndex patch.weight)]
    {Fmark : NilpotentLieFiltration M t}
    {φ : PolynomialShearLieAlgebra patch.weight ℚ →ₗ⁅ℚ⁆ M}
    {marked : Fmark.realification.PolynomialOrbit (fullTaggedVariableWeight (X := X) J)}
    (f : (X → ℤ) → ℝ) (lam : ℝ)
    {cost massThreshold scoreThreshold outputCost outputMass outputScore : ℝ}
    {P : AllocatedExternalCandidateProblem (E := E) A
      (polynomialShearNilmanifold patch.weight s patch.weight_le) Fmark φ marked
      (fun _ z => (patch.shearObservable z : ℂ)) (fun x => ((f x - lam : ℝ) : ℂ))
      cost massThreshold scoreThreshold}
    (out : P.Conclusion outputCost outputMass outputScore)

theorem siteLaw_shear_buffered_score_s2
    (hσ1 : ∀ j, σ j ≤ 1) (H : Fin m → ℝ) (hH : ∀ j, 0 ≤ H j)
    (hchart : ∀ j v, ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (b j)).symm v‖ ≤ H j * ‖v‖)
    (hsmall : ∀ j, H j * (((Fintype.card (I j) : ℝ) + 1) * R j) ≤ 1 / 8)
    (hp : ∀ j, DegreeLE (1 : X → ℕ) (j.val + 1) (poly j))
    {tagCount : ℕ} (e : Fin tagCount ≃ Σ j, J j) (z : out.retained) :
    outputScore ≤ (out.siteLaw z).mean (fun site =>
      bufferedScalarScore (majorPhasePlateauKernel tagCount)
        (fullTaggedBufferedCoordinates e poly (fun j => (P.centerLift j).val))
        (fun x lifts => (patch.ofTaggedWeightedShearOrbit e out.ambient).value
          (Sum.elim (fun i => (x i : ℝ)) (fun i => (lifts i : ℝ))))
        f lam (A.physical z.val site)) := by
  sorry

end AllocatedExternalCandidateProblem.Conclusion
end Erdos3.VectorPolynomial

end

end OAI
end
