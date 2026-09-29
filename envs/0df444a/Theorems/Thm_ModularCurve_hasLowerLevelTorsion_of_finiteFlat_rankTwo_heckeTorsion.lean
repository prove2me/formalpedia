-- Prove2me | Theorems.Thm_ModularCurve_hasLowerLevelTorsion_of_finiteFlat_rankTwo_heckeTorsion
-- name    : ModularCurve.hasLowerLevelTorsion_of_finiteFlat_rankTwo_heckeTorsion
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:52.414366+00:00
-- url     : https://prove2.me/theorems/57df5a5a-3aef-58db-90f7-6980553e2af5
-- title:
--   Finite flat rank-two module at q forces lower-level 𝔪-torsion
-- statement:
--   Let $N \ge 1$ and let $q$ be a prime with $q \nmid N$ and $q \ne 2$. Assume the predicates `HeckeInputsAll` and `HeckeOperatorsCommuteBar` at both levels $N q$ and $N$, the latter asserting that the operators `heckeOperatorBar` at the two levels commute pairwise, so that `heckeModuleBar` makes the degree-zero divisor class group $\mathrm{JZero}(M) = \mathrm{Pic}^0$ of the level-$M$ modular function field over $\overline{\mathbb Q}$ a module over $\mathbb T = \mathbb Z[X_\ell : \ell \text{ prime}]$, with `heckeGen` $\ell = X_\ell$. Let $A$ be a valuation subring of $\overline{\mathbb Q}$ with $q$ a nonunit of $A$, and let $I_A$ be the image in $\mathrm{Gal}(\overline{\mathbb Q}/\mathbb Q)$ of its inertia subgroup. Let $\mathfrak m \subset \mathbb T$ be maximal with $q \in \mathfrak m$, and assume $X_{\ell} - (\ell+1) \notin \mathfrak m$ for some prime $\ell \nmid Nq$. Let $k$ be a field and $V$ a two-dimensional $k$-vector space carrying a $k$-commuting action of $\mathrm{Gal}(\overline{\mathbb Q}/\mathbb Q)$, with an injective Galois-equivariant additive map $\iota \colon V \to \mathrm{JZero}(Nq)$ whose image lies in the $q$-torsion and in the $\mathfrak m$-torsion $\mathrm{torsionBySet}_{\mathbb T}(\mathfrak m)$. Let $n \colon \mathrm{Gal}(\overline{\mathbb Q}/\mathbb Q) \to \mathbb N$ satisfy $\sigma(\zeta) = \zeta^{n(\sigma)}$ for all $\sigma \in I_A$ and all $q$-th roots of unity $\zeta$, with $\det(\sigma \mid V) = n(\sigma)$ in $k$, $n(\sigma) \ne 0$ in $k$ for all $\sigma \in I_A$, and $n(\sigma) \ne 1$ in $k$ for some $\sigma \in I_A$. Finally let $H$ be a commutative ring which is a cocommutative Hopf algebra, finite and flat as a module over the subring [`GaloisRep.ratLocalizedAt`](def/GaloisRep_Flat.html#L8) $q$ of rationals with denominator coprime to $q$, and let $e$ be a bijection from `WithConv` of the $\overline{\mathbb Q}$-points $H \to_{\mathrm{alg}} \overline{\mathbb Q}$ onto $V$ taking the multiplication of `WithConv` to addition and matching the Galois action: if $g$ is $\sigma$ composed with $f$ pointwise on $H$, then $e(g) = \sigma \cdot e(f)$. Then, for the module structure `heckeModuleBar` $N$ on $\mathrm{JZero}(N)$, `HasLowerLevelTorsion` holds for the set `primesOf` $(Nq)$ of prime factors of $Nq$, $\mathfrak m$ and $\mathrm{JZero}(N)$: there is $y \ne 0$ in $\mathrm{JZero}(N)$ with $n \cdot y = 0$ for every natural number $n$ whose image lies in $\mathfrak m$, and $(X_\ell - b) \cdot y = 0$ for every prime $\ell \nmid Nq$ and every $b \in \mathbb Z$ with $X_\ell - b \in \mathfrak m$.
--
--   This is the geometric core of Mazur's principle at the residue characteristic, i.e. the case $\ell = q$ exactly dividing the level of Ribet's level-lowering theorem, with the construction of the two-dimensional Galois module inside $J_0(Nq)[q] \cap J_0(Nq)[\mathfrak m]$, together with its finite flat prolongation $H$, taken as hypotheses. It is used by [`ModularCurve.hasLowerLevelTorsion_jZero_of_isPeuRamifieeAt`](thm.html#ModularCurve.hasLowerLevelTorsion_jZero_of_isPeuRamifieeAt) and by [`ModularCurve.hasLowerLevelTorsion_of_finiteFlat_rankTwo_heckeTorsion_of_five_le`](thm.html#ModularCurve.hasLowerLevelTorsion_of_finiteFlat_rankTwo_heckeTorsion_of_five_le), where the hypotheses on $V$ are supplied by the $q$-torsion of a semistable elliptic curve that is peu ramifiée at $q$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_hasLowerLevelTorsion_of_finiteFlat_rankTwo_heckeTorsion.lean

import Mathlib
import Definitions.Def_ModularCurve_JZeroNeronAtPData

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open ModularCurve

theorem ModularCurve.hasLowerLevelTorsion_of_finiteFlat_rankTwo_heckeTorsion
    (N q : ℕ) [NeZero N] [Fact q.Prime] (hqN : ¬ q ∣ N) (hq2 : q ≠ 2)
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
