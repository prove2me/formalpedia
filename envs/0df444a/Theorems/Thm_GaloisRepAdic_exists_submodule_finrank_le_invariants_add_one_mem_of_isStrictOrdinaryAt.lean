-- Prove2me | Theorems.Thm_GaloisRepAdic_exists_submodule_finrank_le_invariants_add_one_mem_of_isStrictOrdinaryAt
-- name    : GaloisRepAdic.exists_submodule_finrank_le_invariants_add_one_mem_of_isStrictOrdinaryAt
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:46.235172+00:00
-- url     : https://prove2.me/theorems/2ccd8445-0dcf-5f91-b5ed-50bbd5bbf6da
-- title:
--   Strictly ordinary first-order classes lie in a small local subspace at p
-- statement:
--   Let $k$ be a finite field, $p$ an odd prime with $\mathrm{char}\,k=p$, and let $\bar\rho$ be a residual Galois representation over $k$: a $k$-vector space $V$ with $\dim_k V=2$ together with a homomorphism $\bar\rho\colon \mathrm{Gal}(\overline{\mathbb Q}/\mathbb Q)\to \mathrm{End}_k(V)$ factoring through a finite level. Write $\mathrm{ad}^0\bar\rho$ for the subrepresentation of trace-zero endomorphisms of $V$ under conjugation, and let its restriction along `primeLocalToGlobal (pPrime p)`, the map from $\mathrm{Gal}(\overline{\mathbb Q_p}/\mathbb Q_p)$ to the global Galois group, be the local representation at $p$. The assertion is that there is a $k$-submodule $L$ of $H^1$ of this local representation which is finite-dimensional, satisfies $\dim_k L\le \dim_k (\mathrm{ad}^0\bar\rho)^{\mathrm{Gal}(\overline{\mathbb Q_p}/\mathbb Q_p)}+1$, and has the following property. Let $\rho_A$ be an adic Galois representation over the dual numbers $k[\varepsilon]$ (a free $k[\varepsilon]$-module of rank $2$ with an adically continuous Galois homomorphism into its endomorphisms) which is strictly ordinary at $p$, that is: $p$ lies in the maximal ideal of $k[\varepsilon]$, and for every valuation subring $P$ of $\overline{\mathbb Q}$ with $p$ a non-unit of $P$ there is a submodule spanned by the first vector of a basis of $\rho_A$'s module, stable under the decomposition subgroup of $P$, such that inertia in $P$ acts trivially on the quotient, and each $\sigma$ in the decomposition subgroup acts by a scalar $x$ on the line and by a scalar $z$ modulo it, with $x-az\in (p^n)$ whenever $\sigma$ raises all $p^n$-th roots of unity to the $a$-th power. Let furthermore $\rho_d\colon \mathrm{Gal}(\overline{\mathbb Q}/\mathbb Q)\to (k[\varepsilon]\text{-valued units } \mathrm{End}_k(V)[\varepsilon])^\times$ be a dual lift of $\bar\rho$, i.e. the first component of $\rho_d\sigma$ is $\bar\rho\sigma$, and suppose there are bases $b$ of $\rho_A$'s module over $k[\varepsilon]$ and $\bar b$ of $V$ over $k$ for which the matrix of $\rho_A(\sigma)$ in $b$ corresponds, under the identification of matrices over $k[\varepsilon]$ with dual numbers of matrices, to the pair of matrices of the two components of $\rho_d\sigma$ in $\bar b$. Then for every $1$-cocycle $c$ of $\mathrm{ad}^0\bar\rho$ whose value at $\sigma$ is the cochain $(\rho_d\sigma)_{\text{second component}}\cdot\bar\rho(\sigma)^{-1}$, the image of the class of $c$ under the restriction map in degree $1$ along `primeLocalToGlobal (pPrime p)` lies in $L$.
--
--   This is the local bound at $p$ for the strictly ordinary deformation condition in the form used in the Taylor–Wiles Selmer group count: a single subspace $L$, depending only on $\bar\rho$, of dimension at most $h^0(\mathbb Q_p,\mathrm{ad}^0\bar\rho)+1$, containing the restriction at $p$ of the class of every first-order deformation that is strictly ordinary at $p$ (Wiles, Proposition 1.9(iv)). It feeds the bound on the span of dual-number classes used in [`ResidualGaloisRep.exists_taylorWilesPrimes_finrank_span_dualNumberClasses_le_strictOrdinary`](thm.html#ResidualGaloisRep.exists_taylorWilesPrimes_finrank_span_dualNumberClasses_le_strictOrdinary).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_GaloisRepAdic_exists_submodule_finrank_le_invariants_add_one_mem_of_isStrictOrdinaryAt.lean

import Mathlib
import Definitions.Def_GaloisRep_AdZero
import Definitions.Def_GaloisRep_StrictOrdinary
import Definitions.Def_GroupCohomology_TangentSpace
import Definitions.Def_ExtEndgame_ProductionDatum

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory groupCohomology TrivSqZeroExt ExtCitation

theorem GaloisRepAdic.exists_submodule_finrank_le_invariants_add_one_mem_of_isStrictOrdinaryAt
    {k : Type} [Field k] [Finite k] (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2) [CharP k p]
    (ρbar : ResidualGaloisRep k) :
    ∃ L : Submodule k (H1 (Rep.res (primeLocalToGlobal (pPrime p)) ρbar.adZero)),
      FiniteDimensional k L ∧
      Module.finrank k L ≤
        Module.finrank k (Rep.res (primeLocalToGlobal (pPrime p)) ρbar.adZero).ρ.invariants + 1 ∧
      ∀ (ρA : GaloisRepAdic (DualNumber k)), ρA.IsStrictOrdinaryAt p →
        ∀ ρd : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) →* (DualNumber (Module.End k ρbar.V))ˣ,
          IsDualLift ρbar.ρ.toHomUnits ρd →
          (∃ (b : Module.Basis (Fin 2) (DualNumber k) ρA.V) (bbar : Module.Basis (Fin 2) k ρbar.V),
            ∀ σ, LinearMap.toMatrix b b (ρA.ρ σ) =
              Matrix.dualNumberEquiv.symm
                ⟨LinearMap.toMatrix bbar bbar ((ρd σ : DualNumber (Module.End k ρbar.V)).fst),
                  LinearMap.toMatrix bbar bbar ((ρd σ : DualNumber (Module.End k ρbar.V)).snd)⟩) →
          ∀ c : cocycles₁ ρbar.adZero,
            (∀ σ, ((c : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) →
                ↥(LinearMap.ker (LinearMap.trace k ρbar.V))) σ : Module.End k ρbar.V) =
              dualLiftToCochain ρbar.ρ.toHomUnits ρd σ) →
            (groupCohomology.map (primeLocalToGlobal (pPrime p))
              (𝟙 (Rep.res (primeLocalToGlobal (pPrime p)) ρbar.adZero)) 1).hom (H1π ρbar.adZero c) ∈ L := by sorry
