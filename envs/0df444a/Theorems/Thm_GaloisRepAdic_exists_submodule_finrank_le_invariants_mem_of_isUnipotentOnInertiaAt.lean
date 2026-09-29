-- Prove2me | Theorems.Thm_GaloisRepAdic_exists_submodule_finrank_le_invariants_mem_of_isUnipotentOnInertiaAt
-- name    : GaloisRepAdic.exists_submodule_finrank_le_invariants_mem_of_isUnipotentOnInertiaAt
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:46.235172+00:00
-- url     : https://prove2.me/theorems/c1ff670c-1380-5d12-8fdf-adedc914621b
-- title:
--   Unipotent deformations restrict into a small local subspace at ℓ
-- statement:
--   Let $k$ be a finite field of characteristic $p$ with $p$ prime and $p \neq 2$, let $\bar\rho$ be a residual Galois representation over $k$ (a $k$-vector space $V$ of dimension $2$ together with a homomorphism $\bar\rho \colon \mathrm{Gal}(\overline{\mathbb{Q}}/\mathbb{Q}) \to \mathrm{End}_k(V)$ factoring through a finite level), and let $\ell$ be a prime with $\ell \neq p$ such that $\bar\rho$ is not unramified at $\ell$, i.e. some valuation subring $P$ of $\overline{\mathbb{Q}}$ with $\ell$ in its non-units carries an element of its inertia subgroup over $\mathbb{Q}$ acting non-trivially. Then there is a $k$-submodule $L$ of $H^1$ of the restriction of $\mathrm{ad}^0\bar\rho$ — the kernel of the trace on $\mathrm{End}_k(V)$ with the induced Galois action — along `primeLocalToGlobal ℓ`, the map from $\mathrm{Gal}(\overline{\mathbb{Q}_\ell}/\mathbb{Q}_\ell)$ to $\mathrm{Gal}(\overline{\mathbb{Q}}/\mathbb{Q})$, such that $L$ is finite-dimensional, $\dim_k L$ is at most the dimension of the invariants of that restricted representation, and the following holds: for every $\rho_A$ a rank-two free adically continuous Galois representation over the dual numbers $k[\varepsilon]$ all of whose inertia elements over $\ell$ have characteristic polynomial $(X-1)^2$, for every homomorphism $\rho_d \colon \mathrm{Gal}(\overline{\mathbb{Q}}/\mathbb{Q}) \to (\mathrm{End}_k(V)[\varepsilon])^\times$ whose first component is $\bar\rho$, such that in suitable bases of $\rho_A.V$ over $k[\varepsilon]$ and of $V$ over $k$ the matrix of $\rho_A(\sigma)$ is the dual-number matrix assembled from the matrices of the two components of $\rho_d(\sigma)$ for all $\sigma$, and for every $1$-cocycle $c$ of $\mathrm{ad}^0\bar\rho$ whose underlying function equals $\sigma \mapsto (\rho_d \sigma)_{\mathrm{snd}} \cdot \bar\rho(\sigma)^{-1}$ in $\mathrm{End}_k(V)$, the image of the class of $c$ under the degree-one restriction map along `primeLocalToGlobal ℓ` lies in $L$.
--
--   This is the local dimension bound at a prime $\ell \neq p$ where the residual representation ramifies, for the minimally ramified (unipotent inertia) deformation condition: the restrictions of all such first-order deformation classes fit into a subspace of $H^1(\mathbb{Q}_\ell, \mathrm{ad}^0\bar\rho)$ of dimension at most $h^0(\mathbb{Q}_\ell, \mathrm{ad}^0\bar\rho)$, so that such primes make no net contribution to the Greenberg–Wiles count. It is used in [`ResidualGaloisRep.exists_taylorWilesPrimes_finrank_span_dualNumberClasses_le_strictOrdinary`](thm.html#ResidualGaloisRep.exists_taylorWilesPrimes_finrank_span_dualNumberClasses_le_strictOrdinary), the Selmer-group estimate underlying the Taylor–Wiles argument.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_GaloisRepAdic_exists_submodule_finrank_le_invariants_mem_of_isUnipotentOnInertiaAt.lean

import Mathlib
import Definitions.Def_GaloisRep_AdZero
import Definitions.Def_GaloisRep_LocalConditions
import Definitions.Def_GroupCohomology_TangentSpace
import Definitions.Def_ExtEndgame_ProductionDatum

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory groupCohomology TrivSqZeroExt ExtCitation

theorem GaloisRepAdic.exists_submodule_finrank_le_invariants_mem_of_isUnipotentOnInertiaAt
    {k : Type} [Field k] [Finite k] (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2) [CharP k p]
    (ρbar : ResidualGaloisRep k) (ℓ : Nat.Primes) (hℓp : (ℓ : ℕ) ≠ p)
    (hram : ¬ ρbar.IsUnramifiedAt ℓ) :
    ∃ L : Submodule k (H1 (Rep.res (primeLocalToGlobal ℓ) ρbar.adZero)),
      FiniteDimensional k L ∧
      Module.finrank k L ≤
        Module.finrank k (Rep.res (primeLocalToGlobal ℓ) ρbar.adZero).ρ.invariants ∧
      ∀ (ρA : GaloisRepAdic (DualNumber k)), ρA.IsUnipotentOnInertiaAt ℓ →
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
            (groupCohomology.map (primeLocalToGlobal ℓ)
              (𝟙 (Rep.res (primeLocalToGlobal ℓ) ρbar.adZero)) 1).hom (H1π ρbar.adZero c) ∈ L := by sorry
