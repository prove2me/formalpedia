-- Prove2me | Theorems.Thm_NumberField_LevelArith_exists_restrict_and_torsionBy_sClassGroupRep_linearEquiv_sClassTorsionP
-- name    : NumberField.LevelArith.exists_restrict_and_torsionBy_sClassGroupRep_linearEquiv_sClassTorsionP
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:56.923973+00:00
-- url     : https://prove2.me/theorems/3144e583-cadf-584c-8508-aa20d1cc6032
-- title:
--   Transporting p-torsion of the S-class group to the level representation
-- statement:
--   Fix a prime $p$ and a finite set $S$ of rational primes, and let $K \le L$ be intermediate fields of $\mathbb{Q}$ in $\overline{\mathbb{Q}}$, each of finite degree over $\mathbb{Q}$, with $\overline{\mathbb{Q}}$'s intermediate field $L$ viewed over $K$ (written `levelField K L hKL`, the extension of scalars of $L$ to an intermediate field of $\overline{\mathbb{Q}}/K$) normal over $K$, and assume `IsNormalLevel K L`, i.e. $g s g^{-1}$ lies in the fixing subgroup of $L$ for every $g$ in the fixing subgroup of $K$ and every $s$ in the fixing subgroup of $L$. The assertion is the existence of three items. First, a monoid homomorphism $\tau$ from the fixing subgroup of $K$ in $\mathrm{Aut}_{\mathbb{Q}}(\overline{\mathbb{Q}})$ to $\mathrm{Aut}_{\mathbb{Q}}(L)$, together with the compatibility that $\gamma(y) = \tau(\gamma)(y)$ in $\overline{\mathbb{Q}}$ for all such $\gamma$ and all $y \in L$; thus $\tau(\gamma)$ is the restriction of $\gamma$ to $L$. Second, a $\mathbb{Z}/p$-linear equivalence $e$ between the $p$-torsion submodule of the quotient of $\mathrm{Additive}(\mathrm{Cl}(\mathcal{O}_L))$ by the submodule spanned by the classes of the primes of $L$ above $S$ — the module underlying `sClassGroupRep ↥L ↥L S`, taken with $E = F = L$, so with no ambient Galois action — and the module underlying `sClassTorsionP K L hKL S p`, namely the $p$-torsion of the corresponding $S$-class group quotient for `levelField K L hKL`, as a $\mathbb{Z}/p$-representation of the fixing subgroup of $K$ obtained by restriction along `levelGal K L hKL`. Third, the equivariance of $e$, stated on representatives: whenever $x$ is represented by the class of $c \in \mathrm{Cl}(\mathcal{O}_L)$ and $x'$ by the class of `classGroupAut ℚ ↥L (τ γ) c`, the image of $c$ under transport of ideals along $\tau(\gamma)$, one has $e(x') = \rho(\gamma)(e(x))$ for the representation $\rho$ of `sClassTorsionP K L hKL S p`.
--
--   This is the transport lemma identifying the $\mathbb{Z}/p$-module underlying the level representation `sClassTorsionP K L hKL S p` with the $p$-torsion of the $S$-class group of $L$ itself, the action of the fixing subgroup of $K$ being given by restriction of automorphisms to $L$ followed by transport of ideal classes. It is used in the construction of the isomorphism [`groupCohomology.finiteDimensional_and_nonempty_cyclotomicQuotientH2Rep_biprod_trivial_iso`](thm.html#groupCohomology.finiteDimensional_and_nonempty_cyclotomicQuotientH2Rep_biprod_trivial_iso), where class-group computations carried out over $L$ have to be read as statements about a representation of the Galois group over $K$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_NumberField_LevelArith_exists_restrict_and_torsionBy_sClassGroupRep_linearEquiv_sClassTorsionP.lean

import Mathlib
import Definitions.Def_GroupCohomology_ContinuousUnramified
import Definitions.Def_DualSelmer_ExtConditions
import Definitions.Def_ExtCitation_KummerBridge
import Definitions.Def_GroupCohomology_ContinuousUnramifiedLevel
import Definitions.Def_GroupCohomology_ContinuousUnramifiedLevelMap
import Definitions.Def_NumberField_LevelArithmeticModP
import Definitions.Def_NumberField_SelmerRepModP

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory MonoidalCategory Module Limits groupCohomology ExtCitation NumberField.LevelArith IsDedekindDomain
open scoped Classical NumberField NumberField.LevelArith TensorProduct Pointwise

theorem NumberField.LevelArith.exists_restrict_and_torsionBy_sClassGroupRep_linearEquiv_sClassTorsionP
    {p : ℕ} [Fact p.Prime] (S : Finset Nat.Primes)
    (K L : IntermediateField ℚ (AlgebraicClosure ℚ)) [FiniteDimensional ℚ ↥K] [FiniteDimensional ℚ ↥L]
    (hKL : K ≤ L) [Normal ↥K ↥(levelField K L hKL)] (hnorm : IsNormalLevel K L) :
    ∃ (τ : ↥K.fixingSubgroup →* (↥L ≃ₐ[ℚ] ↥L)) (_ : ∀ (γ : ↥K.fixingSubgroup) (y : ↥L), (γ : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)) (y : AlgebraicClosure ℚ) = ((τ γ y : ↥L) : AlgebraicClosure ℚ))
      (e : ↥(Submodule.torsionBy ℤ (sClassGroupRep ↥L ↥L (S : Set Nat.Primes)) (p : ℤ)) ≃ₗ[ZMod p] sClassTorsionP K L hKL S p),
      ∀ (γ : ↥K.fixingSubgroup) (x x' : ↥(Submodule.torsionBy ℤ (sClassGroupRep ↥L ↥L (S : Set Nat.Primes)) (p : ℤ))) (c : ClassGroup (𝓞 ↥L)),
        (x : sClassGroupRep ↥L ↥L (S : Set Nat.Primes)) = Submodule.Quotient.mk (Additive.ofMul c) →
        (x' : sClassGroupRep ↥L ↥L (S : Set Nat.Primes)) = Submodule.Quotient.mk (Additive.ofMul (classGroupAut ℚ ↥L (τ γ) c)) →
          e x' = (sClassTorsionP K L hKL S p).ρ γ (e x) := by sorry
