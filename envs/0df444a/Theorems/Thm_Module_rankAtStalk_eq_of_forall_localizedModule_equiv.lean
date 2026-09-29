-- Prove2me | Theorems.Thm_Module_rankAtStalk_eq_of_forall_localizedModule_equiv
-- name    : Module.rankAtStalk_eq_of_forall_localizedModule_equiv
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:55.610395+00:00
-- url     : https://prove2.me/theorems/2cfd8116-3e98-5423-9373-01d28966db38
-- title:
--   Rank at stalk is invariant under local isomorphism
-- statement:
--   Let $R$ and $A$ be commutative rings in a common universe, with $A$ an $R$-algebra that is module-finite over $R$. Let $M$ and $N$ be additive groups carrying compatible $R$- and $A$-module structures (a scalar tower $R \to A \to M$, resp. $N$), each finite and flat as an $R$-module. Let $s$ be a subset of $A$ whose generated ideal $\mathrm{Ideal.span}\ s$ is the whole of $A$, and suppose that for every $h \in s$ there exists an $A$-linear isomorphism between the localisations $M[1/h]$ and $N[1/h]$, formed as `LocalizedModule` at the submonoid of powers of $h$ (only the existence of such an isomorphism is assumed, via `Nonempty`, with no compatibility between the isomorphisms for different $h$). The conclusion is an equality of functions on $\mathrm{Spec}\,R$: $\mathrm{rankAtStalk}_R\,M = \mathrm{rankAtStalk}_R\,N$, i.e. for every prime $p$ of $R$ the two modules have the same rank at the stalk at $p$. Note that flatness and finiteness are hypotheses over $R$, while the local isomorphisms are over $A$.
--
--   This is the statement that the locally constant rank function over the base of a finite flat module is unchanged when the module is altered by isomorphisms over an open cover of $\mathrm{Spec}\,A$. It is used in the construction of relative effective Cartier divisors, where it shows that two locally isomorphic ideal sheaves have the same fibrewise degrees; it is cited by [`AlgebraicGeometry.RelEffCartierDiv.exists_I_eq_ker_graphOver_mul`](thm.html#AlgebraicGeometry.RelEffCartierDiv.exists_I_eq_ker_graphOver_mul) and [`AlgebraicGeometry.RelEffCartierDiv.exists_I_eq_mul`](thm.html#AlgebraicGeometry.RelEffCartierDiv.exists_I_eq_mul).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Module_rankAtStalk_eq_of_forall_localizedModule_equiv.lean

import Mathlib.RingTheory.Spectrum.Prime.FreeLocus

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

theorem Module.rankAtStalk_eq_of_forall_localizedModule_equiv
    {R A : Type u} [CommRing R] [CommRing A] [Algebra R A] [Module.Finite R A]
    (M N : Type u) [AddCommGroup M] [Module R M] [Module A M] [IsScalarTower R A M]
    [Module.Finite R M] [Module.Flat R M]
    [AddCommGroup N] [Module R N] [Module A N] [IsScalarTower R A N]
    [Module.Finite R N] [Module.Flat R N] (s : Set A) (hs : Ideal.span s = ⊤)
    (H : ∀ h ∈ s, Nonempty
      (LocalizedModule (Submonoid.powers h) M ≃ₗ[A] LocalizedModule (Submonoid.powers h) N)) :
    Module.rankAtStalk (R := R) M = Module.rankAtStalk N := by sorry
