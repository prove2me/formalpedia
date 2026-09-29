-- Prove2me | Theorems.Thm_Module_faithfullyFlat_pi_of_forall_faithfullyFlat_localizationAway_of_span_eq_top
-- name    : Module.faithfullyFlat_pi_of_forall_faithfullyFlat_localizationAway_of_span_eq_top
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:55.610395+00:00
-- url     : https://prove2.me/theorems/6a91e8a8-cb15-55ba-a8d2-ec0c33904221
-- title:
--   Faithful flatness of a product over a basic open cover
-- statement:
--   Let $S$ be a commutative ring (in a fixed universe), let $k$ be a natural number and let $r : \mathrm{Fin}\,k \to S$ be a finite family of elements whose range generates the unit ideal, i.e. $\mathrm{Ideal.span}(\mathrm{range}\,r) = \top$. Let $S'_i$, for $i \in \mathrm{Fin}\,k$, be commutative rings, each equipped with an $S$-algebra structure and with an algebra structure over the localisation $\mathrm{Localization.Away}\,(r_i) = S[1/r_i]$, these being compatible in the sense that $S \to S[1/r_i] \to S'_i$ is a scalar tower. Assume that for every $i$ the ring $S'_i$ is faithfully flat as a module over $S[1/r_i]$. The conclusion is that the product $\prod_{i \in \mathrm{Fin}\,k} S'_i$ is faithfully flat as an $S$-module, the $S$-module structure being the product of the given $S$-algebra structures.
--
--   This is the standard Zariski-local criterion for faithful flatness along a cover of $\mathrm{Spec}\,S$ by the basic open sets $D(r_i)$ associated with a family generating the unit ideal: faithful flatness of each piece over $S[1/r_i]$ yields faithful flatness of the product over $S$. It is used to produce the faithfully flat base ring of a glued square-root datum in the Čerednik–Drinfeld part of the development, and is the engine of the companion statement [`Module.faithfullyFlat_pi_of_forall_faithfullyFlat`](thm.html#Module.faithfullyFlat_pi_of_forall_faithfullyFlat).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Module_faithfullyFlat_pi_of_forall_faithfullyFlat_localizationAway_of_span_eq_top.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

theorem Module.faithfullyFlat_pi_of_forall_faithfullyFlat_localizationAway_of_span_eq_top
    {S : Type u} [CommRing S] {k : ℕ} (r : Fin k → S) (hr : Ideal.span (Set.range r) = ⊤)
    (S' : Fin k → Type u) [∀ i, CommRing (S' i)] [∀ i, Algebra S (S' i)]
    [∀ i, Algebra (Localization.Away (r i)) (S' i)] [∀ i, IsScalarTower S (Localization.Away (r i)) (S' i)]
    (hff : ∀ i, Module.FaithfullyFlat (Localization.Away (r i)) (S' i)) :
    Module.FaithfullyFlat S (∀ i : Fin k, S' i) := by sorry
