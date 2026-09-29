-- Prove2me | Theorems.Thm_Module_FaithfullyFlat_of_forall_isMaximal_exists_ringHom_field
-- name    : Module.FaithfullyFlat.of_forall_isMaximal_exists_ringHom_field
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:55.610395+00:00
-- url     : https://prove2.me/theorems/cfc9a8e0-a5c1-5133-8ab0-de3ac60d3e16
-- title:
--   Flatness plus field-valued points over all maximal ideals gives faithful flatness
-- statement:
--   Let $B$ and $S$ be commutative rings and let $S$ be a $B$-algebra which is flat as a $B$-module. Assume that for every maximal ideal $\mathfrak m$ of $B$ there exist a field $K$ and a ring homomorphism $\psi \colon S \to K$ such that $\mathfrak m$ is contained in the kernel of the composite $B \to S \xrightarrow{\psi} K$, that is, of $\psi$ composed after the structure map `algebraMap B S`. The conclusion is that $S$ is faithfully flat as a $B$-module. Thus the hypothesis is the existence, for each closed point of $\operatorname{Spec} B$, of a $K$-valued point of $S$ lying over it, for some field $K$ (no algebraic closedness, finiteness or residue-field condition on $K$ is imposed, and $\psi$ is only required to be a ring homomorphism, not a $B$-algebra map); flatness of $B \to S$ is assumed separately.
--
--   This is the standard criterion that a flat ring map whose associated map of spectra hits every closed point of the base is faithfully flat. It is used in the construction of Katz forms of level $p$ on modular curves, where field-valued points of an algebra presented by explicit equations are available over each maximal ideal of the base.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Module_FaithfullyFlat_of_forall_isMaximal_exists_ringHom_field.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u v w

theorem Module.FaithfullyFlat.of_forall_isMaximal_exists_ringHom_field
    {B : Type u} {S : Type v} [CommRing B] [CommRing S] [Algebra B S] [Module.Flat B S]
    (h : ∀ m : Ideal B, m.IsMaximal →
      ∃ (K : Type w) (_ : Field K) (ψ : S →+* K), m ≤ RingHom.ker (ψ.comp (algebraMap B S))) :
    Module.FaithfullyFlat B S := by sorry
