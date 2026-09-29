-- Prove2me | Theorems.Thm_GaloisRepAdic_exists_submodule_finrank_le_invariants_add_one_mem_of_isFlatAt
-- name    : GaloisRepAdic.exists_submodule_finrank_le_invariants_add_one_mem_of_isFlatAt
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:46.235172+00:00
-- url     : https://prove2.me/theorems/f0500520-5a21-5ff7-b69e-6c25a8b46d9a
-- title:
--   Local bound for flat first-order deformation classes at p
-- statement:
--   Let $k$ be a finite field of characteristic $p$ with $p$ an odd prime, and let $\bar\rho$ be a residual Galois representation over $k$: a $k$-vector space $V$ with $\dim_k V = 2$ together with a homomorphism $\bar\rho\colon \mathrm{Gal}(\overline{\mathbb Q}/\mathbb Q) \to \mathrm{End}_k(V)$ factoring through a finite level. Write $\mathrm{ad}^0\bar\rho$ for the subrepresentation of the adjoint representation carried by the kernel of $\mathrm{tr}_k\colon \mathrm{End}_k(V)\to k$, and restrict it along the homomorphism $\mathrm{Gal}(\overline{\mathbb Q_p}/\mathbb Q_p)\to \mathrm{Gal}(\overline{\mathbb Q}/\mathbb Q)$ obtained by restricting scalars to $\mathbb Q$ and then restricting to $\overline{\mathbb Q}$. The assertion is that there is a $k$-submodule $L$ of $H^1(\mathrm{Gal}(\overline{\mathbb Q_p}/\mathbb Q_p), \mathrm{ad}^0\bar\rho)$ which is finite-dimensional over $k$, satisfies $\dim_k L \le \dim_k (\mathrm{ad}^0\bar\rho)^{\mathrm{Gal}(\overline{\mathbb Q_p}/\mathbb Q_p)} + 1$, and contains the restriction of every class arising as follows. Let $\rho_A$ be an adic Galois representation over the dual numbers $k[\varepsilon]$ (a free $k[\varepsilon]$-module of rank $2$ with an adically continuous action) which is flat at $p$ in the sense of `IsFlatAt`, i.e. the residue field of $k[\varepsilon]$ is finite and for each ideal $I$ with finite quotient the $I$-level quotient of $\rho_A$ is realised, compatibly with the Galois action, by the points of a finite flat cocommutative Hopf algebra over [`GaloisRep.ratLocalizedAt p`](def/GaloisRep_Flat.html#L8). Let $\rho_d\colon \mathrm{Gal}(\overline{\mathbb Q}/\mathbb Q)\to (\mathrm{End}_k(V)[\varepsilon])^\times$ be a dual lift of $\bar\rho$ (its constant term is $\bar\rho(\sigma)$ for all $\sigma$) such that, in suitable bases $b$ of $\rho_A.V$ over $k[\varepsilon]$ and $\bar b$ of $V$ over $k$, the matrix of $\rho_A(\sigma)$ corresponds under `Matrix.dualNumberEquiv` to the pair of matrices of the two components of $\rho_d(\sigma)$. Let $c$ be a $1$-cocycle of $\mathrm{ad}^0\bar\rho$ whose value at $\sigma$ equals $(\rho_d\sigma)_\varepsilon\,\bar\rho(\sigma)^{-1}$ in $\mathrm{End}_k(V)$. Then the image of the class of $c$ under the degree-one restriction map along $\mathrm{Gal}(\overline{\mathbb Q_p}/\mathbb Q_p)\to \mathrm{Gal}(\overline{\mathbb Q}/\mathbb Q)$ (taken with the identity on the restricted representation) lies in $L$.
--
--   This is the local dimension estimate at $p$ for the finite-flat deformation condition, in the shape in which it enters the Selmer-group count of the Taylor–Wiles argument (Darmon–Diamond–Taylor, §2.4, Proposition 2.27(a)): the local condition at $p$ exceeds $h^0(\mathbb Q_p, \mathrm{ad}^0\bar\rho)$ by at most one. It is used in the construction of sets of Taylor–Wiles primes bounding the dimension of the space of first-order deformations satisfying the strictly ordinary, respectively flat, conditions.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_GaloisRepAdic_exists_submodule_finrank_le_invariants_add_one_mem_of_isFlatAt.lean

import Mathlib
import Definitions.Def_GaloisRep_AdZero
import Definitions.Def_GaloisRep_Flat
import Definitions.Def_GroupCohomology_TangentSpace
import Definitions.Def_ExtEndgame_ProductionDatum

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory groupCohomology TrivSqZeroExt ExtCitation

theorem GaloisRepAdic.exists_submodule_finrank_le_invariants_add_one_mem_of_isFlatAt
    {k : Type} [Field k] [Finite k] (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2) [CharP k p]
    (ρbar : ResidualGaloisRep k) :
    ∃ L : Submodule k (H1 (Rep.res (primeLocalToGlobal (pPrime p)) ρbar.adZero)),
      FiniteDimensional k L ∧
      Module.finrank k L ≤
        Module.finrank k (Rep.res (primeLocalToGlobal (pPrime p)) ρbar.adZero).ρ.invariants + 1 ∧
      ∀ (ρA : GaloisRepAdic (DualNumber k)), ρA.IsFlatAt p →
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
