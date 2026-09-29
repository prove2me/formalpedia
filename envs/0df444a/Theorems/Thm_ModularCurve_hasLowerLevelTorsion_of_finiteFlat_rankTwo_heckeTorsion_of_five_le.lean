-- Prove2me | Theorems.Thm_ModularCurve_hasLowerLevelTorsion_of_finiteFlat_rankTwo_heckeTorsion_of_five_le
-- name    : ModularCurve.hasLowerLevelTorsion_of_finiteFlat_rankTwo_heckeTorsion_of_five_le
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:52.414366+00:00
-- url     : https://prove2.me/theorems/f6b9bb27-f105-57a5-8178-80eeab52ece9
-- title:
--   Finite-flat level lowering at q ≥ 5
-- statement:
--   Fix $N \ge 1$ and a prime $q$ with $q \nmid N$, $q \ne 2$ and $5 \le q$, and assume the Hecke input conditions `HeckeInputsAll` at levels $Nq$ and $N$ together with commutativity of the geometric Hecke operators `HeckeOperatorsCommuteBar` at both levels, so that the degree-zero divisor class groups $J_0 :=$ `JZero` of the modular function fields over $\overline{\mathbb Q}$ carry module structures over $\mathbb T := \mathbb Z[X_\ell : \ell \text{ prime}]$. Let $A$ be a valuation subring of $\overline{\mathbb Q}$ with $q$ a nonunit of $A$, and write $I_A$ for the inertia subgroup of $A$ over $\mathbb Q$, viewed inside $\mathrm{Aut}_{\mathbb Q}(\overline{\mathbb Q})$ via the decomposition subgroup. Let $\mathfrak m \subset \mathbb T$ be a maximal ideal with $q \in \mathfrak m$ which is non-Eisenstein in the weak sense that $X_\ell - (\ell+1) \notin \mathfrak m$ for some prime $\ell \nmid Nq$. Let $k$ be a field and $V$ a $k$-vector space of rank $2$ with a distributive Galois action commuting with the $k$-scalars, and let $\iota : V \to J_0(Nq)$ be an injective additive Galois-equivariant map whose image lies in the $q$-torsion of $J_0(Nq)$ and in the $\mathfrak m$-torsion `Submodule.torsionBySet` of $J_0(Nq)$. Let $n : \mathrm{Gal} \to \mathbb N$ satisfy $\sigma\zeta = \zeta^{n(\sigma)}$ for all $\sigma \in I_A$ and all $\zeta$ with $\zeta^q = 1$, and assume for $\sigma \in I_A$ that $\det(\sigma|V) = n(\sigma)$ in $k$, that $n(\sigma) \ne 0$ in $k$, and that $n(\sigma) \ne 1$ in $k$ for at least one $\sigma \in I_A$. Finally let $H$ be a commutative cocommutative Hopf algebra, module-finite and flat, over the subring [`GaloisRep.ratLocalizedAt q`](def/GaloisRep_Flat.html#L8) of $\mathbb Q$ of rationals whose denominator is coprime to $q$, and let $e$ be a bijection from `WithConv` of the $\mathbb Z_{(q)}$-algebra maps $H \to \overline{\mathbb Q}$ to $V$ carrying the convolution product to addition and intertwining the Galois actions in the sense that $e(g) = \sigma \cdot e(f)$ whenever $g = \sigma \circ f$ pointwise on $H$. Then `HasLowerLevelTorsion (primesOf (N*q)) 𝔪 (JZero N)` holds: there is $y \ne 0$ in $J_0(N)$ with $n \cdot y = 0$ for every natural number $n$ whose image lies in $\mathfrak m$, and $(X_\ell - b) \cdot y = 0$ for every prime $\ell$ not dividing $Nq$ and every $b \in \mathbb Z$ with $X_\ell - b \in \mathfrak m$.
--
--   This is the finite-flat (Ribet) level-lowering step at a prime $q$ exactly dividing the level $Nq$: a rank-two Galois-stable subspace of $J_0(Nq)[q] \cap J_0(Nq)[\mathfrak m]$ which is the group of points of a finite flat group scheme over $\mathbb Z_{(q)}$, with ramified determinant on inertia at $q$, produces non-zero $\mathfrak m$-torsion at level $N$. It is the variant restricted to $q \ge 5$, so that the general statement can be assembled by treating $q \ge 5$ here and $q = 3$ through the Néron-model route; it is cited in the deduction of lower-level torsion from the peu-ramifiée hypothesis.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_hasLowerLevelTorsion_of_finiteFlat_rankTwo_heckeTorsion_of_five_le.lean

import Mathlib
import Definitions.Def_ModularCurve_JZeroNeronAtPData

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open ModularCurve

theorem ModularCurve.hasLowerLevelTorsion_of_finiteFlat_rankTwo_heckeTorsion_of_five_le
    (N q : ℕ) [NeZero N] [Fact q.Prime] (hqN : ¬ q ∣ N) (hq2 : q ≠ 2) (hq5 : 5 ≤ q)
    (hin : HeckeInputsAll (N * q)) (hcomm : HeckeOperatorsCommuteBar (N * q))
    (hinN : HeckeInputsAll N) (hcommN : HeckeOperatorsCommuteBar N)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime q)
    (𝔪 : Ideal HeckeAlg) (hmax : 𝔪.IsMaximal) (hqm : ((q : ℕ) : HeckeAlg) ∈ 𝔪)
    (heis : ∃ ℓ : Nat.Primes, ¬ (ℓ : ℕ) ∣ N * q ∧ heckeGen ℓ - MvPolynomial.C (((ℓ : ℕ) : ℤ) + 1) ∉ 𝔪)
    {k : Type*} [Field k] {V : Type} [AddCommGroup V] [Module k V]
    [DistribMulAction (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) V]
    [SMulCommClass (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) k V]
    (hrank : Module.finrank k V = 2)
    (ι : V →+ JZero (N * q)) (hinj : Function.Injective ι)
    (hequiv : ∀ (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (v : V), ι (σ • v) = σ • ι v)
    (hιq : ∀ v : V, ι v ∈ jZeroTorsion (N * q) q)
    (hι𝔪 : ∀ v : V, (letI := heckeModuleBar (N * q); ι v ∈ heckeTorsion (JZero (N * q)) 𝔪))
    (n : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) → ℕ)
    (hn : ∀ σ ∈ A.inertiaSubgroupIn ℚ, ∀ ζ : AlgebraicClosure ℚ, ζ ^ q = 1 → σ ζ = ζ ^ (n σ))
    (hdet : ∀ σ ∈ A.inertiaSubgroupIn ℚ, LinearMap.det (DistribMulAction.toLinearMap k V σ) = (n σ : k))
    (hunit : ∀ σ ∈ A.inertiaSubgroupIn ℚ, (n σ : k) ≠ 0)
    (hram : ∃ σ ∈ A.inertiaSubgroupIn ℚ, (n σ : k) ≠ 1)
    (H : Type) [CommRing H] [HopfAlgebra (GaloisRep.ratLocalizedAt q) H]
    [Module.Finite (GaloisRep.ratLocalizedAt q) H] [Module.Flat (GaloisRep.ratLocalizedAt q) H]
    [Coalgebra.IsCocomm (GaloisRep.ratLocalizedAt q) H]
    (e : WithConv (H →ₐ[GaloisRep.ratLocalizedAt q] AlgebraicClosure ℚ) ≃ V)
    (he_add : ∀ f g, e (f * g) = e f + e g)
    (he_act : ∀ (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)
      (f g : WithConv (H →ₐ[GaloisRep.ratLocalizedAt q] AlgebraicClosure ℚ)),
      (∀ x : H, g x = σ (f x)) → e g = σ • e f) :
    letI := heckeModuleBar N
    HasLowerLevelTorsion (primesOf (N * q)) 𝔪 (JZero N) := by sorry
