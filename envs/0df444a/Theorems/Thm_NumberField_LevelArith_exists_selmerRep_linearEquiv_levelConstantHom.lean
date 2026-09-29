-- Prove2me | Theorems.Thm_NumberField_LevelArith_exists_selmerRep_linearEquiv_levelConstantHom
-- name    : NumberField.LevelArith.exists_selmerRep_linearEquiv_levelConstantHom
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:56.923973+00:00
-- url     : https://prove2.me/theorems/1f4a1048-a190-563d-a0cf-86de1162cc33
-- title:
--   Kummer isomorphism for the mod p Selmer module, twisted
-- statement:
--   Fix a prime $p$ and a finite set $S$ of rational primes containing $p$ (as the element `pPrime p`). Let $K, L$ be intermediate fields of $\mathbb{Q}$ in $\overline{\mathbb{Q}} =$ `AlgebraicClosure ℚ`, both finite over $\mathbb{Q}$, with $K \le L$, such that $L$ satisfies `IsUnramifiedOutside S`, i.e. $L/\mathbb{Q}$ is finite and for every prime $q \notin S$ and every valuation subring $A$ of $\overline{\mathbb{Q}}$ with $q$ in the nonunits of $A$, the image in $\mathrm{Gal}(\overline{\mathbb{Q}}/\mathbb{Q})$ of the inertia subgroup of $A$ over $\mathbb{Q}$ lies in the fixing subgroup of $L$; assume moreover that the level field `levelField K L hKL` (namely $L$ regarded as an intermediate field over $K$) is normal over $K$, and that some primitive $p$-th root of unity $\zeta \in \overline{\mathbb{Q}}$ lies in $L$. Write $\Gamma_K =$ `K.fixingSubgroup` and let $H =$ `L.fixingSubgroup.subgroupOf K.fixingSubgroup` be the subgroup of $\Gamma_K$ consisting of elements fixing $L$. The assertion is that there is a $\mathbb{Z}/p$-linear isomorphism $e$ from `selmerRep K L hKL S p` — the inflation along `levelGal` to $\Gamma_K$ of the mod $p$ Selmer representation of the extension $K \subseteq$ `levelField K L hKL` relative to the height-one primes of $\mathcal{O}_K$ lying over the primes of $S$ — onto the submodule `levelConstantHom` of maps $\varphi : H \to \mathbb{Z}/p$ that are additive, $\varphi(gh) = \varphi(g) + \varphi(h)$, and satisfy the condition `IsLevelConstantSr₁` at $S$ for the homomorphism $H \to \Gamma_K \to \mathrm{Gal}(\overline{\mathbb{Q}}/\mathbb{Q})$ given by the two subgroup inclusions, such that $e$ is $\Gamma_K$-equivariant up to the mod $p$ cyclotomic character: for all $g \in \Gamma_K$, all $x$ in the Selmer module and all $s, t \in H$ with $g^{-1} s g = t$ in $\Gamma_K$, one has $e(\rho(g)x)(s) = \mathrm{cycloChar}_p(g) \cdot e(x)(t)$, the character value being taken in $\mathbb{Z}/p$.
--
--   This is the Kummer-theoretic description of the mod $p$ Selmer module of a number field containing $\mu_p$ and unramified outside $S$: classes of $S$-units modulo $p$-th powers correspond to additive $S$-level-constant characters of the Galois group of $L$, the correspondence being Galois-equivariant only after a twist by the cyclotomic character. It is used in the computation comparing the dimension of the continuous $S$-ramified $H^1$ with the dimension of the invariants of the Selmer module tensored with the coefficient module.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_NumberField_LevelArith_exists_selmerRep_linearEquiv_levelConstantHom.lean

import Mathlib
import Definitions.Def_GroupCohomology_ContinuousUnramified
import Definitions.Def_DualSelmer_ExtConditions
import Definitions.Def_ExtCitation_KummerBridge
import Definitions.Def_GroupCohomology_ContinuousUnramifiedLevel
import Definitions.Def_GroupCohomology_ContinuousUnramifiedLevelMap
import Definitions.Def_NumberField_LevelArithmeticModP
import Definitions.Def_NumberField_SelmerRepModP
import Definitions.Def_GroupCohomology_LevelConstantHom

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory MonoidalCategory Module groupCohomology ExtCitation NumberField.LevelArith IsDedekindDomain
open scoped Classical NumberField NumberField.LevelArith

theorem NumberField.LevelArith.exists_selmerRep_linearEquiv_levelConstantHom
    {p : ℕ} [Fact p.Prime] (S : Finset Nat.Primes) (hpS : pPrime p ∈ S)
    (K L : IntermediateField ℚ (AlgebraicClosure ℚ)) (hL : L.IsUnramifiedOutside S)
    [FiniteDimensional ℚ ↥K] [FiniteDimensional ℚ ↥L]
    (hKL : K ≤ L) [Normal ↥K ↥(levelField K L hKL)]
    (ζ : AlgebraicClosure ℚ) (hζ : IsPrimitiveRoot ζ p) (hζL : ζ ∈ L) :
    ∃ e : (selmerRep K L hKL S p) ≃ₗ[ZMod p]
        ↥(levelConstantHom (K.fixingSubgroup.subtype.comp (L.fixingSubgroup.subgroupOf K.fixingSubgroup).subtype) S (ZMod p) (ZMod p)),
      ∀ (g : ↥K.fixingSubgroup) (x : selmerRep K L hKL S p) (s t : ↥(L.fixingSubgroup.subgroupOf K.fixingSubgroup)),
        (g⁻¹ * s * g : ↥K.fixingSubgroup) = t →
          (e ((selmerRep K L hKL S p).ρ g x) : ↥(L.fixingSubgroup.subgroupOf K.fixingSubgroup) → ZMod p) s =
            ((((cycloChar p).comp K.fixingSubgroup.subtype) g : (ZMod p)ˣ) : ZMod p) *
              (e x : ↥(L.fixingSubgroup.subgroupOf K.fixingSubgroup) → ZMod p) t := by sorry
