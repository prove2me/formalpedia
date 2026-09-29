-- Prove2me | Theorems.Thm_HeckeEis_coresHom_resHom_apply
-- name    : HeckeEis.coresHom_resHom_apply
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:55.058405+00:00
-- url     : https://prove2.me/theorems/0176efcf-a54c-5bb2-ac68-b44815428116
-- title:
--   Corestriction after restriction is multiplication by the index
-- statement:
--   Let $G$ be a group, $H \le G$ a subgroup of finite index, and $A$ an additive abelian group. For a homomorphism $\varphi$ from the additive group $\mathrm{Additive}\,G$ (the group $G$ written additively) to $A$, and for any $g \in G$, the assertion is the equality
--   $$\mathrm{coresHom}_H(\mathrm{resHom}_H \varphi)(g) \;=\; [G:H]\cdot \varphi(g),$$
--   with $[G:H]$ acting on $A$ through the natural $\mathbb{N}$-action. Here $\mathrm{resHom}_H$ sends $\varphi$ to its composite with the inclusion $H \hookrightarrow G$, read additively, and $\mathrm{coresHom}_H$ sends a homomorphism $\psi$ on $\mathrm{Additive}\,H$ to the homomorphism whose value at $g$ is the sum over the finitely many cosets $q \in G/H$ of $\psi$ evaluated at the element $\mathrm{transferAux}_H(g,q) = ((g \cdot q)_{\mathrm{out}})^{-1}\,(g\, q_{\mathrm{out}}) \in H$, where $q \mapsto q_{\mathrm{out}}$ is the chosen coset representative map and $g \cdot q$ the left translation action of $g$ on $G/H$. Thus, evaluated at a single element, the composite of restriction to $H$ followed by the transfer map built from these representatives is multiplication by the index.
--
--   This is the push–pull (projection) formula for the transfer, or corestriction, in degree one: $\mathrm{cores}_H \circ \mathrm{res}_H = [G:H]$ on homomorphisms $G \to A$. It is used in the construction of Hecke operators on Eisenstein-type homomorphism groups, being cited in the computation of [`HeckeEis.heckeOperatorHom_apply_of_conj_invariant`](thm.html#HeckeEis.heckeOperatorHom_apply_of_conj_invariant) and in the level-raising analysis of $q$-new support for normalised eigenforms at odd primes.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_HeckeEis_coresHom_resHom_apply.lean

import Definitions.Def_Gamma0HeckeOperatorHom

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open Subgroup

theorem HeckeEis.coresHom_resHom_apply {G : Type*} [Group G] (H : Subgroup G) {A : Type*}
    [AddCommGroup A] [H.FiniteIndex] (φ : Additive G →+ A) (g : G) :
    HeckeEis.coresHom H (HeckeEis.resHom H φ) (Additive.ofMul g) =
      H.index • φ (Additive.ofMul g) := by sorry
