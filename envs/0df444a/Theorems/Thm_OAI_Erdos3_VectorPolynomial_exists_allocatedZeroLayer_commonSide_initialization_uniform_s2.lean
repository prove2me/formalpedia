-- Prove2me | Theorems.Thm_OAI_Erdos3_VectorPolynomial_exists_allocatedZeroLayer_commonSide_initialization_uniform_s2
-- name    : OAI.Erdos3.VectorPolynomial.exists_allocatedZeroLayer_commonSide_initialization_uniform_s2
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-17T11:41:02.619107+00:00
-- url     : https://prove2.me/theorems/ce0dad45-7e25-4239-bed1-f9f1a9b626e4
-- title:
--   Uniform initialization of an allocated external candidate problem with zero polynomial layers and common side lengths
-- statement:
--   Let $s$ be a natural number. Then there is a natural number $C \ge 2$ with the following property.
--
--   Let $G$ and $X$ be finite types. Take zero layers ($m = 0$): $I, E, J$ are families of types indexed by $\operatorname{Fin} 0$ (so empty families) and $n : \operatorname{Fin} 0 \to \mathbb{N}$; let $B$ assign a finite type to each element of `LayerSamplerAxis I n`; let $U$, $b$, $R$, $\sigma$, $hb$, $o$, $hR$, $h\sigma$, `poly` and $hm$ be the (necessarily trivial) families of subspaces, bases, reals, polynomials and hypotheses of the same shape as in OpenAI's sampler setting (all indexed by $\operatorname{Fin} 0$), with the lattice instances. Let $S$ be a `LayerSamplerScale B U b R σ` (OpenAI's structure containing a positive natural number `S.value`). Let $n_0$ be a natural number with a bijection $G \simeq \operatorname{Fin} n_0$, let $P : \operatorname{Fin} n_0 \to \mathbb{N}$ with all $P_j \ne 0$, and assume $X$ is nonempty (an element of $X$ is given). Let $p, a, \Lambda, \mathrm{surplus}, \mathrm{extra}$ be reals and $d_0$ a natural number with:
--
--   - $p \ge 0$, $a \ge 0$, $\Lambda \in [0, 1]$, $0 < \mathrm{surplus} \le 1$, $\mathrm{extra} \ge 0$;
--   - $P_j \le \texttt{S.value} \le e^{\mathrm{extra}} P_j$ for all $j$;
--   - `RelativePatchAbsoluteRule s n₀ p a Λ d₀` (OpenAI's predicate: the base case of the relative patch argument for boxes of $n_0$ distinct comparable primes at least $e^p$; it yields `RelativePatchSliceConclusion` with target $\Lambda$, rank bound $d_0$ and cost $p$ for every $[0,1]$-valued $(s+2)$-progression-free function of mean at least $a$);
--   - every $P_j$ is prime, $P$ is injective, $P_j \le 2^{n_0 + 1} P_k$ for all $j, k$, and $e^p \le P_j$ for all $j$.
--
--   Let $N : X \to \mathbb{N}$ with $N_x \ge$ `unconditionedSpatialWidthCutoff` $\bigl(|\texttt{LayerSamplerVariables G I n B}| \cdot \texttt{S.value},\ \tau,\ \texttt{unconditionedCollisionWidth P surplus}\bigr)$ for every $x$, where $\tau$ = `unconditionedSpatialTrimFraction |X| surplus` $= \mathrm{surplus} / (32(|X| + 1))$, `unconditionedSpatialWidthCutoff B τ L` $= \max\bigl(4/\tau,\ 8(1+B)\max(8\,\texttt{probabilityProfileLipschitz}, L)/\tau\bigr)$ and `unconditionedCollisionWidth P surplus` $= 32 \bigl(\prod_j P_j\bigr)^2 / \mathrm{surplus}$ (here $\prod_j P_j$ is the size of $\prod_j \mathbb{Z}/P_j$). Let $f : \mathbb{Z}^X \to \mathbb{R}$ with $f(x) \in [0, 1]$ for all $x$ in `integerBox N` $= \prod_x [0, N_x)$, such that $\{x \in \texttt{integerBox N} : f(x) \ne 0\}$ contains no arithmetic progression $a', a' + d, \dots, a' + (s+1)d$ with $d \ne 0$ (`IntegerVectorAPFree … (s + 2)`), and with $a + \mathrm{surplus} \le \mathbb{E}_{x \in \texttt{integerBox N}} f(x)$.
--
--   Put $q = p + \mathrm{extra} + |\texttt{LayerSamplerVariables G I n B}| + 2$, $D = \min(d_0, \lfloor p + \mathrm{extra} \rfloor)$ and
--   $$\mathrm{mass} = \frac{\mathrm{surplus}/4}{(D+1)(s+1)^D} \, e^{-(q+2)^C}.$$
--   Then there exist a proof $A$ of `AllocatedExternalCandidateSampler B U b S hb o hR hσ N poly hm τ 1 (fun _ => 1) {0} 0` (OpenAI's sampler conditions, with trim fraction $\tau$, narrowing $1$, all strides $1$, the single residue cell $0$ and center $0$), a natural number $d$ and a `PolynomialPatch (LayerSamplerVariables G I n B) s d` named `patch` (OpenAI's structure of weights, polynomial slots and a kernel with Lipschitz constant `kernel.lip`), such that $d \le d_0$, $d \le D$, `patch.kernel.lip` $\le e^{(q+2)^C}$, the coefficient mass (sum of absolute values of coefficients, `realPolynomialMass`) of each center polynomial `patch.form.center j` is at most $(q+2)^C$, and there exists an `AllocatedExternalCandidateProblem A (polynomialShearNilmanifold patch.weight s _) (RationalTorus.trivialFiltration s) 0 1 (fun _ y => patch.shearObservable y) (fun x => f x - Λ) (p + extra) mass (exp (-(q+2)^C))` named $Q$ (the arguments $0$ and $1$ are the Lie algebra map into the trivial filtration and the marked polynomial orbit; OpenAI's structure: a finite set of productive paths of law-mass at least `mass`, a local chart for each with cost $p + \mathrm{extra}$ and a common center lift, frozen sides at most $e^{p+\mathrm{extra}}$, and a local candidate for each whose score for the observable `patch.shearObservable` on OpenAI's polynomial shear nilmanifold and the weight $x \mapsto f(x) - \Lambda$ is at least $e^{-(q+2)^C}$), with $Q$`.centerLift` $=$ `allocatedZeroLayerCenterLift U` (the empty center lift) and, for every productive path $z$, the chart of $z$ keeps every coordinate (`keep` is the constant predicate True).
--
--   Lean: `OAI.Erdos3.VectorPolynomial.exists_allocatedZeroLayer_commonSide_initialization_uniform_s2`, which states OpenAI's `OAI.Erdos3.VectorPolynomial.exists_allocatedZeroLayer_commonSide_initialization_uniform` (in `lean/OAI/Combinatorics/Progressions/Estimates/AllocatedZeroLayerCommonSideInitializationUniform.lean`); the definitions it uses are in the definitions bundles `OAIE3v2B148`, `OAIE3v2B198` of version 2 of this split (and the bundles they import).
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/Progressions/Estimates/AllocatedZeroLayerCommonSideInitializationUniform.lean (declaration OAI.Erdos3.VectorPolynomial.exists_allocatedZeroLayer_commonSide_initialization_uniform)

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIE3v2B148
import Definitions.Def_OAIE3v2B198

section

namespace OAI

section

namespace Erdos3.VectorPolynomial

open Module Submodule BooleanCubeKernel NilpotentLieFiltration NilpotentLieBCHGroup
open scoped BigOperators Classical TensorProduct

theorem exists_allocatedZeroLayer_commonSide_initialization_uniform_s2 (s : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧
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
      (n₀ : ℕ) (_eG : G ≃ Fin n₀)
      (P : Fin n₀ → ℕ) [∀ j, NeZero (P j)] (_i : X)
      {p a Λ surplus extra : ℝ},
      0 ≤ p → 0 ≤ a → Λ ∈ Set.Icc (0 : ℝ) 1 →
      0 < surplus → surplus ≤ 1 → 0 ≤ extra →
      (∀ j, P j ≤ S.value) →
      (∀ j, (S.value : ℝ) ≤ Real.exp extra * (P j : ℝ)) →
      ∀ (d₀ : ℕ), RelativePatchAbsoluteRule s n₀ p a Λ d₀ →
      (∀ j, (P j).Prime) → Function.Injective P →
      (∀ j k, P j ≤ 2 ^ (n₀ + 1) * P k) →
      (∀ j, Real.exp p ≤ (P j : ℝ)) →
      ∀ (N : X → ℕ),
      (∀ x, unconditionedSpatialWidthCutoff
        ((Fintype.card (LayerSamplerVariables G I n B) : ℝ) * S.value)
        (unconditionedSpatialTrimFraction (Fintype.card X) surplus)
        (unconditionedCollisionWidth P surplus) ≤ (N x : ℝ)) →
      ∀ (f : (X → ℤ) → ℝ),
      (∀ x ∈ integerBox N, f x ∈ Set.Icc (0 : ℝ) 1) →
      IntegerVectorAPFree {x | x ∈ integerBox N ∧ f x ≠ 0} (s + 2) →
      a + surplus ≤ (𝔼 x ∈ integerBox N, f x) →
      let τ := unconditionedSpatialTrimFraction (Fintype.card X) surplus
      let q := p + extra + (Fintype.card (LayerSamplerVariables G I n B) : ℝ) + 2
      let D := min d₀ ⌊p + extra⌋₊
      let mass := ((surplus / 4) / ((D + 1) * (s + 1) ^ D : ℕ)) *
        Real.exp (-((q + 2) ^ C))
      ∃ (A : AllocatedExternalCandidateSampler B U b S hb o hR hσ
          N poly hm τ 1 (fun _ => 1) {0} 0)
        (d : ℕ) (patch : PolynomialPatch (LayerSamplerVariables G I n B) s d),
        d ≤ d₀ ∧ d ≤ D ∧
        (patch.kernel.lip : ℝ) ≤ Real.exp ((q + 2) ^ C) ∧
        (∀ j, realPolynomialMass (patch.form.center j) ≤ (q + 2) ^ C) ∧
        letI := polynomialShearIndexFintype patch.weight patch.weight_pos
        ∃ Q : AllocatedExternalCandidateProblem (E := E) A
          (polynomialShearNilmanifold patch.weight s patch.weight_le)
          (RationalTorus.trivialFiltration s) 0 1
          (fun _ y => (patch.shearObservable y : ℂ))
          (fun x => ((f x - Λ : ℝ) : ℂ))
          (p + extra) mass (Real.exp (-((q + 2) ^ C))),
          Q.centerLift = allocatedZeroLayerCenterLift U ∧
          ∀ z, (Q.chart z).keep = fun _ => True := by
  sorry

end Erdos3.VectorPolynomial

end

end OAI
end
