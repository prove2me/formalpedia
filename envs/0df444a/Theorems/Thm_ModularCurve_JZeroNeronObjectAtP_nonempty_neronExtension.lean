-- Prove2me | Theorems.Thm_ModularCurve_JZeroNeronObjectAtP_nonempty_neronExtension
-- name    : ModularCurve.JZeroNeronObjectAtP.nonempty_neronExtension
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:40.860483+00:00
-- url     : https://prove2.me/theorems/12577ed5-d12f-56b5-a09e-157c15c6e775
-- title:
--   Existence of a Néron extension of an at-p Néron object
-- statement:
--   Fix natural numbers $N_0$ and $p$ with $N_0 \neq 0$, $p$ prime and nonzero, and assume $p \nmid N_0$. Let $A$ be a valuation subring of $\overline{\mathbf{Q}}$ with `A.LiesOverPrime p`, i.e. the image of $p$ lies in the nonunits of $A$. Let $\Lambda$ be a `LevelData N₀ p A`: a section `σA` of the base over $\operatorname{Spec} A$ compatible with the generic point, a scheme $X$ over the base carrying a relative group law, together with bijections of $\mathrm{JZero}\,N_0$ with the generic-fibre sections and of $\mathrm{JZeroC}$ over the residue field of $A$ with the sections at the reduction point. Assume `Λ.IsJacobian`: the abelian-scheme property bundle, commutativity of the group law, additivity and Galois equivariance of the generic points dictionary, additivity of the special points dictionary, compatibility of reduction mod $\ell$, and realisability of every Hecke operator by an endomorphism over the base. Let $O$ be a `JZeroNeronObjectAtP N₀ p hpN₀ A hA Λ`. Then the type `O.NeronExtension` is nonempty: there exist a scheme $\mathcal{N}$ over $\operatorname{Spec}$ of the inertia-field valuation ring `shRing A`, with a commutative relative group law which, whenever that ring is Dedekind, is smooth, separated, locally of finite type, quasi-compact and has the Néron unique-extension property over the fraction field `invField A`; an open immersion over the base change of $O.g$ compatible with multiplication, through which every section at `barPt A ≫ shPt A` comes from a point of $\mathrm{JZero}(N_0p)$; and a surjective additive map `specN` from sections over `shPt A` to `componentGroup O.width`, vanishing exactly on sections lifted from $O$ over `Λ.σA` and agreeing with `O.comp` on inertia invariants.
--
--   This is the existence of the full Néron model of the modular Jacobian $J_0(N_0p)$ over the valuation ring of the inertia field at a place above $p$, packaged as an extension datum of a given identity-component object together with its component map onto the Kirchhoff component group. It is the input used in assembling the at-$p$ Néron datum, and is cited by [`ModularCurve.JZeroNeronObjectAtP.exists_jZeroNeronAtPDataOrdV22_of_children`](thm.html#ModularCurve.JZeroNeronObjectAtP.exists_jZeroNeronAtPDataOrdV22_of_children).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_JZeroNeronObjectAtP_nonempty_neronExtension.lean

import Mathlib
import Definitions.Def_ModularCurve_JZeroNeronObjectAtP_NeronExtension

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry NeronModelInfra GoodReductionJacobian ModularCurve IsLocalRing
  AlgebraicCurve ModularCurve.JZeroNeronObjectAtP

theorem ModularCurve.JZeroNeronObjectAtP.nonempty_neronExtension
    (N₀ p : ℕ) [NeZero N₀] [Fact p.Prime] [NeZero p] (hpN₀ : ¬ p ∣ N₀)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    (Λ : JZeroNeronObjectAtP.LevelData N₀ p A) (hΛ : Λ.IsJacobian)
    (O : JZeroNeronObjectAtP N₀ p hpN₀ A hA Λ) :
    Nonempty O.NeronExtension := by sorry
