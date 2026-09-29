-- Prove2me | Theorems.Thm_GaloisRepAdic_isEquiv_baseChangeAlong_baseChangeAlong
-- name    : GaloisRepAdic.isEquiv_baseChangeAlong_baseChangeAlong
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:46.235172+00:00
-- url     : https://prove2.me/theorems/d2b2663c-be9a-58a2-893d-a37e0710deaa
-- title:
--   Iterated base change equals base change along the composite
-- statement:
--   Let $A$, $B$, $C$ be commutative local rings, let $f \colon A \to B$ and $g \colon B \to C$ be ring homomorphisms with hypotheses `hf : IsLocalHom f` and `hg : IsLocalHom g` (non-units are carried to non-units), and let $\rho$ be an object of [`GaloisRepAdic A`](def/GaloisRep_Adic.html#L16): a type $V$ carrying the structure of a finite free $A$-module with $\operatorname{rank}_A V = 2$, together with a monoid homomorphism $\rho$ from the group of $\mathbb{Q}$-algebra automorphisms of `AlgebraicClosure ℚ` to $\operatorname{End}_A V$ satisfying the adic continuity condition [`GaloisActionIsAdicContinuous`](def/GaloisRep_Adic.html#L9), namely that for every $n \in \mathbb{N}$ there is an intermediate field $L$ of $\mathbb{Q} \subseteq$ `AlgebraicClosure ℚ`, finite-dimensional over $\mathbb{Q}$, such that $\rho(\sigma)v - v \in \mathfrak{m}_A^n \cdot V$ for all $v \in V$ and all $\sigma$ fixing $L$ pointwise. The conclusion asserts `IsEquiv` between two objects of [`GaloisRepAdic C`](def/GaloisRep_Adic.html#L16): the result of base changing $\rho$ along $f$ and then along $g$, whose module is $C \otimes_B (B \otimes_A V)$ with $\sigma$ acting as the iterated `LinearMap.baseChange` of $\rho(\sigma)$, and the base change of $\rho$ along the composite $g \circ f$ (local by `RingHom.isLocalHom_comp`), whose module is $C \otimes_A V$ with $\sigma$ acting as the base change of $\rho(\sigma)$. That is, there exists a $C$-linear isomorphism between these two modules intertwining the two Galois actions.
--
--   This is the transitivity of extension of scalars for two-dimensional adic Galois representations: pushing a representation forward along $f$ and then along $g$ gives the same representation, up to equivalence, as pushing it forward along $g \circ f$. It is pure bookkeeping used wherever a representation over a local ring is transported along two successive local homomorphisms, for instance a Hecke–Galois representation along a point of a Hecke algebra followed by a further map, and it is cited in the modularity-lifting arguments concerning patching data for local Hecke algebras.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_GaloisRepAdic_isEquiv_baseChangeAlong_baseChangeAlong.lean

import Mathlib
import Definitions.Def_GaloisRep_Adic

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem GaloisRepAdic.isEquiv_baseChangeAlong_baseChangeAlong
    {A B C : Type} [CommRing A] [IsLocalRing A] [CommRing B] [IsLocalRing B] [CommRing C] [IsLocalRing C]
    (f : A →+* B) (hf : IsLocalHom f) (g : B →+* C) (hg : IsLocalHom g) (ρ : GaloisRepAdic A) :
    ((ρ.baseChangeAlong f hf).baseChangeAlong g hg).IsEquiv
      (ρ.baseChangeAlong (g.comp f) (RingHom.isLocalHom_comp g f)) := by sorry
