-- Prove2me | Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_isFinite_and_flat_schemeNsmul_of_isUnit
-- name    : GoodReductionJacobian.RelativeGroupLaw.isFinite_and_flat_schemeNsmul_of_isUnit
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:53.637625+00:00
-- url     : https://prove2.me/theorems/25d1dbd4-4739-590b-aa9a-61b92958a706
-- title:
--   Multiplication by a unit n on an abelian scheme is finite and flat
-- statement:
--   Let $R$ be a noetherian commutative ring, $J$ a scheme and $f \colon J \to \operatorname{Spec} R$ a morphism. Let $L$ be a relative group law for $f$ over $R$: for every scheme $T$ and every structure morphism $t \colon T \to \operatorname{Spec} R$, a multiplication, a unit and an inversion on the set $\{\varphi \colon T \to J \mid \varphi \text{ followed by } f = t\}$ of $T$-points of $f$, satisfying associativity, the two unit laws and left inverses, and natural in $T$ under composition with morphisms $\psi \colon T' \to T$ over $\operatorname{Spec} R$. Assume `AbelianSchemePropertyBundle`, i.e. $f$ is smooth and proper, every fibre $f^{-1}(s)$ of the underlying continuous map is connected, and $f$ admits some relative group law; assume further that $L$ is commutative, i.e. $L.\mathrm{mul}\ t\ x\ y = L.\mathrm{mul}\ t\ y\ x$ for all $t$ and all $T$-points $x, y$. Let $n \in \mathbb{N}$ be such that the image of $n$ in $R$ is a unit. Then the endomorphism `L.schemeNsmul n` of $J$ — the morphism underlying the $n$-th $L$-power of the tautological point $\mathrm{id}_J$, formed by the recursion sending $0$ to the unit section and $k+1$ to the $L$-product of the $k$-th power with $\mathrm{id}_J$ — is both finite and flat.
--
--   This is the statement that multiplication by $n$ on an abelian scheme is finite and flat whenever $n$ is invertible on the base, the case of $[n]$ being an isogeny in which no wild behaviour at residue characteristics dividing $n$ occurs. It supplies the finiteness and flatness input for constructions with $n$-torsion and level structures on relative Picard schemes and on Jacobians of curves with good reduction.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_GoodReductionJacobian_RelativeGroupLaw_isFinite_and_flat_schemeNsmul_of_isUnit.lean

import Mathlib
import Definitions.Def_JacJ1Iface
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawKernel

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian

universe u

theorem GoodReductionJacobian.RelativeGroupLaw.isFinite_and_flat_schemeNsmul_of_isUnit
    {R : Type u} [CommRing R] [IsNoetherianRing R]
    {J : Scheme.{u}} {f : J ⟶ Spec (CommRingCat.of R)} (L : RelativeGroupLaw R f)
    (hJ : AbelianSchemePropertyBundle R f)
    (hcomm : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (x y : SchemeHomOver t f),
      L.mul t x y = L.mul t y x)
    (n : ℕ) (hn : IsUnit (n : R)) :
    IsFinite (L.schemeNsmul n) ∧ Flat (L.schemeNsmul n) := by sorry
