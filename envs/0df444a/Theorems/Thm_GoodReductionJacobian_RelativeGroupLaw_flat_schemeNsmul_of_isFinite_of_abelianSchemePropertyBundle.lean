-- Prove2me | Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_flat_schemeNsmul_of_isFinite_of_abelianSchemePropertyBundle
-- name    : GoodReductionJacobian.RelativeGroupLaw.flat_schemeNsmul_of_isFinite_of_abelianSchemePropertyBundle
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:53.637625+00:00
-- url     : https://prove2.me/theorems/2a5e1a39-2855-5300-a4f3-a4a6308eb0e8
-- title:
--   Finite multiplication by n on an abelian scheme is flat
-- statement:
--   Let $R$ be a noetherian commutative ring, $J$ a scheme and $f \colon J \to \operatorname{Spec} R$ a morphism. Let $L$ be a relative group law for $f$: for every scheme $T$ and every $t \colon T \to \operatorname{Spec} R$ a group structure (`mul`, `one`, `inv`, with associativity, both unit laws and left inverse) on the set `SchemeHomOver t f` of morphisms $\varphi \colon T \to J$ with $\varphi$ followed by $f$ equal to $t$, the multiplication being natural in the base: for $\psi \colon T' \to T$ with $\psi$ followed by $t$ equal to $t'$, composition with $\psi$ carries products to products. Assume `AbelianSchemePropertyBundle R f`, that is: $f$ is smooth, $f$ is proper, for every point $s$ of $\operatorname{Spec} R$ the fibre $f^{-1}(s)$ is connected (as a topological space, and nonempty), and $f$ admits some relative group law. Assume further that $L$ is commutative, i.e. `L.mul t x y = L.mul t y x` for all $t$ and all sections $x,y$. Let $n$ be a natural number with $n > 0$, and let `L.schemeNsmul n` be the endomorphism of $J$ obtained as the underlying morphism of the $n$-fold $L$-sum of the tautological point $\mathrm{id}_J \in$ `SchemeHomOver f f` (defined by recursion, the $0$th term being `L.one f`). If this endomorphism $[n] \colon J \to J$ is a finite morphism, then it is flat.
--
--   This is the scheme-theoretic flatness of multiplication by $n$ on an abelian scheme over a noetherian base, deduced from the corresponding statement over a field by the local criterion of flatness applied fibrewise: the hypotheses are those of an abelian scheme presented through a functorial commutative group law on relative points, and finiteness of $[n]$ is assumed rather than proved. It is used to obtain finite flat $n$-torsion subschemes — whence the Hopf-algebra description of the torsion — and, in the modular-curve application, to produce finite flat prolongations of torsion in the relative $\mathrm{Pic}^0$ of a curve with good reduction.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_GoodReductionJacobian_RelativeGroupLaw_flat_schemeNsmul_of_isFinite_of_abelianSchemePropertyBundle.lean

import Mathlib
import Definitions.Def_JacJ1Iface
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawKernel

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory AlgebraicGeometry NeronModelInfra GoodReductionJacobian
set_option maxHeartbeats 800000 in

theorem GoodReductionJacobian.RelativeGroupLaw.flat_schemeNsmul_of_isFinite_of_abelianSchemePropertyBundle
    {R : Type u} [CommRing R] [IsNoetherianRing R]
    {J : Scheme.{u}} {f : J ⟶ Spec (CommRingCat.of R)} (L : RelativeGroupLaw R f)
    (hJ : AbelianSchemePropertyBundle R f)
    (hcomm : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (x y : SchemeHomOver t f),
      L.mul t x y = L.mul t y x)
    (n : ℕ) (hn : 0 < n) (hfin : IsFinite (L.schemeNsmul n)) :
    Flat (L.schemeNsmul n) := by sorry
