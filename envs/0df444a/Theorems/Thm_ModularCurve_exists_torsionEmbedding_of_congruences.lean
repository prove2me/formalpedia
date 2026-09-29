-- Prove2me | Theorems.Thm_ModularCurve_exists_torsionEmbedding_of_congruences
-- name    : ModularCurve.exists_torsionEmbedding_of_congruences
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:52.061738+00:00
-- url     : https://prove2.me/theorems/6a6eb319-b328-593c-9614-cb9b730ff4ce
-- title:
--   Embedding of E[p] into the 𝔪-torsion of J
-- statement:
--   Let $J$ be an abelian group carrying a module structure over the polynomial Hecke algebra `HeckeAlg` $=\mathbb Z[X_\ell : \ell \text{ prime}]$ together with an action of $\mathrm{Gal}(\overline{\mathbb Q}/\mathbb Q)$, where $\overline{\mathbb Q}$ is the algebraic closure `AlgebraicClosure ℚ`, the two actions commuting. Let $N \neq 0$ and let $p$ be a prime with $p \neq 2$. Assume `FrobeniusQuadratic`: for every prime $\ell \nmid Np$, every valuation subring $A \subseteq \overline{\mathbb Q}$ with $\ell$ a non-unit of $A$, every $\sigma$ in the decomposition subgroup of $A$ acting as $x \mapsto x^{\ell}$ on the residue field of $A$, and every $x \in J$ killed by some power of $p$, one has $\sigma^2 x - X_\ell\,(\sigma x) + \ell x = 0$. Let $E$ be a Weierstrass curve over $\mathbb Z$ with $\Delta_E \neq 0$ such that, over $\overline{\mathbb Q}$, the $p$-torsion $E[p]$ of the base change of $E$ to $\mathbb Q$ is nontrivial and its only Galois-stable $\mathbb Z/p$-submodules are $0$ and itself. Let $\mathfrak m$ be a maximal ideal of `HeckeAlg` containing the constant $p$, let $S$ be a finite set of primes, and suppose $X_\ell - a_\ell(E) \in \mathfrak m$ for every prime $\ell \notin S$ with $\ell \nmid \Delta_E$, where $a_\ell(E) = \ell + 1 - \#E(\mathbb F_\ell)$ is computed from the reduction of the given model. Write $J[\mathfrak m]$ for the submodule of elements annihilated by $\mathfrak m$; assume $J[\mathfrak m] \neq 0$ and that there is a Galois number field $F \subseteq \overline{\mathbb Q}$ such that the kernel of the restriction map $\mathrm{Gal}(\overline{\mathbb Q}/\mathbb Q) \to \mathrm{Gal}(F/\mathbb Q)$ fixes $J[\mathfrak m]$ pointwise. Then there exists an injective additive homomorphism $\iota : E[p] \to J$ which commutes with the action of every $\sigma \in \mathrm{Gal}(\overline{\mathbb Q}/\mathbb Q)$ and whose image lies in $J[\mathfrak m]$.
--
--   This is the Boston–Lenstra–Ribet style realisation of an irreducible residual representation inside the $\mathfrak m$-torsion of a Hecke module: congruences $T_\ell \equiv a_\ell(E)$ at almost all good primes, together with the Eichler–Shimura quadratic relation, force $E[p]$ to embed Galois-equivariantly into $J[\mathfrak m]$. It is used in the lower-level torsion statements for the $j=0$ case and in the residual modularity step that divides the level.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_exists_torsionEmbedding_of_congruences.lean

import Mathlib
import Definitions.Def_FreyPackage_LoweringAtUniform
import Definitions.Def_FreyPackage_MazurEichlerShimuraFamily

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open WeierstrassCurve WeierstrassCurve.Affine WeierstrassCurve.Affine.Point
open ModularCurve

theorem ModularCurve.exists_torsionEmbedding_of_congruences
    {J : Type*} [AddCommGroup J] [Module HeckeAlg J]
    [DistribMulAction (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) J]
    [SMulCommClass (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) HeckeAlg J]
    (N p : ℕ) (hN : N ≠ 0) (hp : p.Prime) (hp2 : p ≠ 2)
    (hES : FrobeniusQuadratic (K := ℚ) (L := AlgebraicClosure ℚ) N p J)
    (E : WeierstrassCurve ℤ) (hΔ : E.Δ ≠ 0) (hirr : E.ModRepIsIrreducible p)
    (𝔪 : Ideal HeckeAlg) (hmax : 𝔪.IsMaximal) (hpm : MvPolynomial.C (p : ℤ) ∈ 𝔪)
    (S : Finset Nat.Primes)
    (hcong : ∀ ℓ : Nat.Primes, ℓ ∉ S → E.IsGoodPrimeFor ℓ →
      heckeGen ℓ - MvPolynomial.C (E.apOfModel ℓ) ∈ 𝔪)
    (hfix : ∃ (F : Type) (_ : Field F) (_ : NumberField F) (_ : IsGalois ℚ F)
        (_ : Algebra F (AlgebraicClosure ℚ)) (_ : IsScalarTower ℚ F (AlgebraicClosure ℚ)),
        (AlgEquiv.restrictNormalHom (F := ℚ) (K₁ := AlgebraicClosure ℚ) F).ker ≤
          fixingSubgroup (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (heckeTorsion J 𝔪 : Set J))
    (hne : heckeTorsion J 𝔪 ≠ ⊥) :
    ∃ ι : Submodule.torsionBy ℤ ((E.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)).Point p →+ J,
      Function.Injective ι ∧
      (∀ (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)
        (v : Submodule.torsionBy ℤ ((E.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)).Point p),
        ι (σ • v) = σ • ι v) ∧
      (∀ v, ι v ∈ heckeTorsion J 𝔪) := by sorry
