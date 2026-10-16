-- Prove2me | Theorems.Thm_OAI_Erdos3_VectorPolynomial_exists_allocatedZeroLayer_budgeted_initialization
-- name    : OAI.Erdos3.VectorPolynomial.exists_allocatedZeroLayer_budgeted_initialization
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-16T01:46:40.977608+00:00
-- url     : https://prove2.me/theorems/591ff91f-3c5a-4114-a295-3c718cd099c8
-- title:
--   Zero-layer allocated initialization with polynomial shape and input budgets
-- statement:
--   Let $s, n_0$ be natural numbers. Then there are natural numbers $C_{\mathrm{shape}}, C_{\mathrm{input}}$ with $2 \le C_{\mathrm{shape}} \le C_{\mathrm{input}}$ such that the following holds. Let $G, X$ be finite types; take zero layers, i.e. families $I, E, J$ of types and $n$ indexed by $\mathrm{Fin}\,0$ (with $I_j, J_j$ finite), finite types $B_a$ over `LayerSamplerAxis I n`, subspaces $U_j$, bases $b_j$, $R, \sigma : \mathrm{Fin}\,0 \to \mathbb R$, a proof $hb$ that each $b_j$ spans `projectedIntegerLattice (euclideanSubspace (U j))`, orthonormal bases $o_j$, proofs $hR$, $h\sigma$ of $R_j > 0$ and $\sigma_j > 0$, vector polynomials $\mathrm{poly}_j$ on $X$ with coefficients in $U_j$ (hypothesis $hm$), and `IsZLattice` instances for the lattice sections (all of these are vacuous families since $\mathrm{Fin}\,0$ is empty). Let $S$ be a `LayerSamplerScale` for $(B, U, b, R, \sigma)$ over $G$ (a structure bundling a positive natural number $S.\mathrm{value}$ with width and gap inequalities), let $G \simeq \mathrm{Fin}\,n_0$, let $P : \mathrm{Fin}\,n_0 \to \mathbb N$ with all $P_j \ne 0$, let $X$ have an element, and let $p, a, \Lambda$ be reals with $p \ge 2$, $a \ge 0$, $\Lambda \in [0,1]$. Assume $P_j \le S.\mathrm{value}$ and $S.\mathrm{value} \le \exp(\mathrm{unconditionedCommonSideExtra}\ n_0)\, P_j$ for all $j$ (where `unconditionedCommonSideExtra n` $= \log(1 + n 2^{n+1})$). Let $d_0$ be a natural number with `RelativePatchAbsoluteRule s n₀ p a Λ d₀` (a proposition of OpenAI asserting `RelativePatchSliceConclusion s N f Λ d₀ p` for every box of side lengths $N$ given by $n_0$ distinct primes, pairwise within a factor $2^{n_0+1}$, each at least $e^p$, and every $[0,1]$-valued $f$ on it with $(s+2)$-progression-free support and mean at least $a$). Assume every $P_j$ is prime, $P$ is injective, $P_j \le 2^{n_0+1} P_k$ for all $j, k$, and $e^p \le P_j$ for all $j$. Let $N : X \to \mathbb N$ with
--   $$\mathrm{unconditionedSpatialWidthCutoff}\bigl(|\mathrm{Vars}|\, S.\mathrm{value},\ \tau,\ \mathrm{unconditionedCollisionWidth}(P, e^{-p})\bigr) \le N_x$$
--   for every $x$, where $\mathrm{Vars} =$ `LayerSamplerVariables G I n B`, $\tau =$ `unconditionedSpatialTrimFraction |X| (exp(-p))` $= e^{-p}/(32(|X|+1))$, `unconditionedSpatialWidthCutoff B τ L` $= \max(4/\tau,\ 8(1+B)\max(8\lambda, L)/\tau)$ with $\lambda$ the constant `probabilityProfileLipschitz`, and `unconditionedCollisionWidth P σ` $= 32(\prod_j P_j)^2/\sigma$. Let $f : (X \to \mathbb Z) \to \mathbb R$ take values in $[0,1]$ on `integerBox N` (the $x$ with $0 \le x_i < N_i$), with $\{x \in \mathrm{integerBox}\,N : f(x) \ne 0\}$ free of $(s+2)$-term progressions (`IntegerVectorAPFree`), and $a + e^{-p} \le \mathbb E_{x \in \mathrm{integerBox}\,N} f(x)$. Put $\mathrm{shape} = (p+2)^{C_{\mathrm{shape}}}$ and $\mathrm{input} = (p+2)^{C_{\mathrm{input}}}$.
--
--   Then there exist a proof $A$ of `AllocatedExternalCandidateSampler B U b S hb o hR hσ N poly hm τ 1 (fun _ => 1) {0} 0` (a proposition bundling positivity conditions and positive masses), a natural number $d$ and a `PolynomialPatch Vars s d` `patch` (weights in $[1,s]$, polynomial slot centers, and a kernel with Lipschitz constant `patch.kernel.lip`) such that $d \le d_0$, $d \le \mathrm{shape}$, `patch.kernel.lip` $\le e^{\mathrm{shape}}$, the sum of absolute values of the coefficients (`realPolynomialMass`) of each slot center `patch.form.center j` is at most $\mathrm{shape}$, and, for every choice of topology on $\mathbb R \otimes_{\mathbb Q}$ `PolynomialShearLieAlgebra patch.weight ℚ` making it a Hausdorff topological vector space, there is $M \in \mathbb R_{\ge 0}$ with `patch.ExternalObservableRegularity M input` (a structure: the nilmanifold `polynomialShearNilmanifold patch.weight s _` has geometry complexity at most `input`, the observable `patch.shearObservable` is Lipschitz with a constant at most $e^{\mathrm{input}}$, and it is real with values in $[0,1]$) and there is an `AllocatedExternalCandidateProblem` $Q$ for $A$, the nilmanifold `polynomialShearNilmanifold patch.weight s _`, the filtration `RationalTorus.trivialFiltration s`, the parameters $0$ and $1$, the observable $(\_, y) \mapsto$ `patch.shearObservable y`, the weight $x \mapsto f(x) - \Lambda$, cost `input`, mass threshold $e^{-\mathrm{input}}$ and score threshold $e^{-\mathrm{input}}$ (a structure bundling a finite set of productive paths of law-mass at least the threshold, local charts and candidates with score at least the threshold), such that `Q.centerLift` $=$ `allocatedZeroLayerCenterLift U` (the empty family) and `(Q.chart z).keep` is the always-true predicate for every $z$.
--
--   Lean: `OAI.Erdos3.VectorPolynomial.exists_allocatedZeroLayer_budgeted_initialization` in `lean/OAI/Combinatorics/Progressions/Dynamics/CanonicalZeroLayerBudgetedInitialization.lean` (OpenAI); the definitions it uses are in the definitions bundles `OAIErdos3B1342` of this split (and the bundles they import).
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/Progressions/Dynamics/CanonicalZeroLayerBudgetedInitialization.lean#L262

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIErdos3B1342

namespace OAI

section

namespace Erdos3

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

end Erdos3

end

section

namespace Erdos3.VectorPolynomial
open Module Submodule BooleanCubeKernel NilpotentLieFiltration NilpotentLieBCHGroup
open scoped BigOperators Classical TensorProduct NNReal

theorem exists_allocatedZeroLayer_budgeted_initialization (s n₀ : ℕ) :
    ∃ Cshape Cinput : ℕ, 2 ≤ Cshape ∧ Cshape ≤ Cinput ∧
    ∀ {G X : Type} [Fintype G] [Fintype X]
    {I E J : Fin 0 → Type} [∀ j, Fintype (I j)] [∀ j, Fintype (J j)]
    {n : Fin 0 → ℕ} (B : LayerSamplerAxis I n → Type) [∀ a, Fintype (B a)]
    (U : ∀ j, Submodule ℝ (J j → ℝ))
    (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
    {R σ : Fin 0 → ℝ}
    (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
    (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
    (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
    (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
    (hm : ∀ j e, coefficients (poly j) e ∈ U j)
    [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))],
    ∀ (S : LayerSamplerScale (G := G) B U b R σ)
      (_eG : G ≃ Fin n₀)
      (P : Fin n₀ → ℕ) [∀ j, NeZero (P j)] (_i : X)
      {p a Λ : ℝ},
      2 ≤ p → 0 ≤ a → Λ ∈ Set.Icc (0 : ℝ) 1 →
      (∀ j, P j ≤ S.value) →
      (∀ j, (S.value : ℝ) ≤ Real.exp (unconditionedCommonSideExtra n₀) * (P j : ℝ)) →
      ∀ (d₀ : ℕ), RelativePatchAbsoluteRule s n₀ p a Λ d₀ →
      (∀ j, (P j).Prime) → Function.Injective P →
      (∀ j k, P j ≤ 2 ^ (n₀ + 1) * P k) →
      (∀ j, Real.exp p ≤ (P j : ℝ)) →
      ∀ (N : X → ℕ),
      (∀ x, unconditionedSpatialWidthCutoff
        ((Fintype.card (LayerSamplerVariables G I n B) : ℝ) * S.value)
        (unconditionedSpatialTrimFraction (Fintype.card X) (Real.exp (-p)))
        (unconditionedCollisionWidth P (Real.exp (-p))) ≤ (N x : ℝ)) →
      ∀ (f : (X → ℤ) → ℝ),
      (∀ x ∈ integerBox N, f x ∈ Set.Icc (0 : ℝ) 1) →
      IntegerVectorAPFree {x | x ∈ integerBox N ∧ f x ≠ 0} (s + 2) →
      a + (Real.exp (-p)) ≤ (𝔼 x ∈ integerBox N, f x) →
      let τ := unconditionedSpatialTrimFraction (Fintype.card X) (Real.exp (-p))
      let shape := (p + 2) ^ Cshape
      let input := (p + 2) ^ Cinput
      ∃ (A : AllocatedExternalCandidateSampler B U b S hb o hR hσ
          N poly hm τ 1 (fun _ => 1) {0} 0)
        (d : ℕ) (patch : PolynomialPatch (LayerSamplerVariables G I n B) s d),
        d ≤ d₀ ∧ (d : ℝ) ≤ shape ∧
        (patch.kernel.lip : ℝ) ≤ Real.exp shape ∧
        (∀ j, realPolynomialMass (patch.form.center j) ≤ shape) ∧
        letI := polynomialShearIndexFintype patch.weight patch.weight_pos
        ∀ [TopologicalSpace (ℝ ⊗[ℚ] PolynomialShearLieAlgebra patch.weight ℚ)]
          [IsTopologicalAddGroup (ℝ ⊗[ℚ] PolynomialShearLieAlgebra patch.weight ℚ)]
          [ContinuousSMul ℝ (ℝ ⊗[ℚ] PolynomialShearLieAlgebra patch.weight ℚ)]
          [T2Space (ℝ ⊗[ℚ] PolynomialShearLieAlgebra patch.weight ℚ)],
        ∃ M : ℝ≥0, patch.ExternalObservableRegularity M input ∧
        ∃ Q : AllocatedExternalCandidateProblem (E := E) A
          (polynomialShearNilmanifold patch.weight s patch.weight_le)
          (RationalTorus.trivialFiltration s) 0 1
          (fun _ y => (patch.shearObservable y : ℂ))
          (fun x => ((f x - Λ : ℝ) : ℂ))
          input (Real.exp (-input)) (Real.exp (-input)),
          Q.centerLift = allocatedZeroLayerCenterLift U ∧
          ∀ z, (Q.chart z).keep = fun _ => True := by
  sorry

end Erdos3.VectorPolynomial
end
end OAI
