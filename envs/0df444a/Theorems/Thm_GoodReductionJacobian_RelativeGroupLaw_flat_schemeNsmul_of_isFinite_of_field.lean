-- Prove2me | Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_flat_schemeNsmul_of_isFinite_of_field
-- name    : GoodReductionJacobian.RelativeGroupLaw.flat_schemeNsmul_of_isFinite_of_field
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:53.637625+00:00
-- url     : https://prove2.me/theorems/22a822a9-f62e-5590-bfda-01f2fd11989c
-- title:
--   Flatness of [n] on a smooth proper group scheme over a field
-- statement:
--   Let $k$ be a field, $J$ a scheme and $f : J \to \operatorname{Spec} k$ a morphism. Let $L$ be a relative group law for $f$: for every scheme $T$ and every $t : T \to \operatorname{Spec} k$, a multiplication, unit and inversion on the set of $T$-points $\{\varphi : T \to J \mid \varphi \circ f = t\}$ (written in Lean as `SchemeHomOver t f`), satisfying associativity, the two unit laws and the left inverse law, the multiplication being natural in $T$ along any $\psi : T' \to T$ with $t \circ \psi = t'$. Let $hJ$ be the property bundle asserting that $f$ is smooth, $f$ is proper, the set-theoretic fibre $f^{-1}(s)$ is connected for every point $s$ of $\operatorname{Spec} k$, and that a relative group law for $f$ exists. Let $n$ be a natural number with $0 < n$, and write $[n] : J \to J$ for `L.schemeNsmul n`, the underlying morphism of the $n$-fold $L$-sum of the identity point $\mathrm{id}_J$ viewed as a $J$-point of $f$. Assume $[n]$ is a finite morphism. Then $[n]$ is flat.
--
--   This is the statement that an isogeny-like endomorphism $[n]$ of an abelian scheme over a field is flat, obtained from miracle flatness as in the classical treatment of multiplication by $n$ on an abelian variety. It is used downstream for flatness of $[n]$ on fibres and in the study of $n$-torsion of relative $\mathrm{Pic}^0$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_GoodReductionJacobian_RelativeGroupLaw_flat_schemeNsmul_of_isFinite_of_field.lean

import Mathlib
import Definitions.Def_JacJ1Iface
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawKernel

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry NeronModelInfra GoodReductionJacobian

universe u

theorem GoodReductionJacobian.RelativeGroupLaw.flat_schemeNsmul_of_isFinite_of_field
    {k : Type u} [Field k] {J : Scheme.{u}} {f : J ⟶ Spec (CommRingCat.of k)}
    (L : RelativeGroupLaw k f) (hJ : AbelianSchemePropertyBundle k f)
    (n : ℕ) (hn : 0 < n) (hfin : IsFinite (L.schemeNsmul n)) :
    Flat (L.schemeNsmul n) := by sorry
