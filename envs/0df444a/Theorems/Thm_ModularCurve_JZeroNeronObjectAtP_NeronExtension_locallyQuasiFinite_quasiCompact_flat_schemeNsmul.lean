-- Prove2me | Theorems.Thm_ModularCurve_JZeroNeronObjectAtP_NeronExtension_locallyQuasiFinite_quasiCompact_flat_schemeNsmul
-- name    : ModularCurve.JZeroNeronObjectAtP.NeronExtension.locallyQuasiFinite_quasiCompact_flat_schemeNsmul
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:40.860483+00:00
-- url     : https://prove2.me/theorems/6d123732-9103-5cb1-a81d-7fc5054f7b4b
-- title:
--   Multiplication by m on a Néron extension is quasi-finite and flat
-- statement:
--   Fix natural numbers $N_0$ and $p$, both nonzero, with $p$ prime and $p \nmid N_0$. Let $A$ be a valuation subring of $\overline{\mathbf Q}$ lying over $p$, in the sense that $p$, viewed in $\overline{\mathbf Q}$, belongs to the nonunits of $A$. Let $\Lambda$ be level data of level $N_0$ at $p$ over $A$ — a structure morphism $\sigma_A$ from $\operatorname{Spec} A$ to the base `base p` lifting the generic point, a scheme $X$ over that base carrying a relative group law, and bijections identifying $J_0(N_0)$-points, respectively their residue-field analogues, with sections of $X$ over the generic and the special point — and assume $\Lambda$ satisfies `IsJacobian`: the abelian-scheme property bundle for its structure morphism, commutativity of its group law, additivity and Galois-equivariance of the two point parametrisations, compatibility of reduction of points modulo $\ell$, and realisation of the Hecke algebra by endomorphisms over the base (summarised here). Let $O$ be a level-$N_0p$ Néron object at $p$ over $(A,\Lambda)$, and let $F$ be a Néron extension of $O$, consisting of a scheme `F.Nfull` over `shBase A` with commutative relative group law `F.LN` over the ring `shRing A`, the Néron model property bundle, an open immersion over the base from the base change of $O$'s group scheme, and a surjective specialisation homomorphism onto the component group with kernel the sections coming from $O$. Finally let $m$ be a natural number with $0 < m$. Then the endomorphism `F.LN.schemeNsmul m` of `F.Nfull`, namely the $m$-fold multiple of the identity section for the group law `F.LN`, is locally quasi-finite, quasi-compact and flat.
--
--   This is the standard statement that multiplication by $m$ on a Néron model of an abelian variety is quasi-finite and flat, here for the full Néron model of $J_0(N_0p)$ over the valuation ring attached to $A$. It is used in constructing the $m$-torsion of that Néron model as a finite flat group scheme with its Hopf algebra and point parametrisation.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_JZeroNeronObjectAtP_NeronExtension_locallyQuasiFinite_quasiCompact_flat_schemeNsmul.lean

import Mathlib
import Definitions.Def_ModularCurve_JZeroNeronObjectAtP_NeronExtension

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian ModularCurve IsLocalRing
  AlgebraicCurve ModularCurve.JZeroNeronObjectAtP

theorem ModularCurve.JZeroNeronObjectAtP.NeronExtension.locallyQuasiFinite_quasiCompact_flat_schemeNsmul
    (N₀ p : ℕ) [NeZero N₀] [Fact p.Prime] [NeZero p] (hpN₀ : ¬ p ∣ N₀)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    (Λ : JZeroNeronObjectAtP.LevelData N₀ p A) (hΛ : Λ.IsJacobian)
    (O : JZeroNeronObjectAtP N₀ p hpN₀ A hA Λ) (F : O.NeronExtension) (m : ℕ) (hm : 0 < m) :
    LocallyQuasiFinite (F.LN.schemeNsmul m) ∧ QuasiCompact (F.LN.schemeNsmul m) ∧ Flat (F.LN.schemeNsmul m) := by sorry
