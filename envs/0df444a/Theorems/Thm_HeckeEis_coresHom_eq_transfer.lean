-- Prove2me | Theorems.Thm_HeckeEis_coresHom_eq_transfer
-- name    : HeckeEis.coresHom_eq_transfer
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:55.058405+00:00
-- url     : https://prove2.me/theorems/866bba0c-2e48-5436-969c-e8a3faae5f62
-- title:
--   Coset-sum corestriction equals the transfer homomorphism
-- statement:
--   Let $G$ be a group and $H \le G$ a subgroup of finite index, let $A$ be an additive abelian group, and let $\varphi \colon \mathrm{Additive}\,H \to A$ be an additive group homomorphism, i.e. a homomorphism from $H$ written additively into $A$. Recall that [`HeckeEis.coresHom`](def/Gamma0HeckeOperatorHom.html#L238) sends $\varphi$ to the additive homomorphism $\mathrm{Additive}\,G \to A$ given, after choosing for each coset $q \in G/H$ its canonical representative $q_{\mathrm{out}}$, by the coset sum $$g \longmapsto \sum_{q \in G/H} \varphi\bigl((g \cdot q)_{\mathrm{out}}^{-1}\, g\, q_{\mathrm{out}}\bigr),$$ the argument of $\varphi$ lying in $H$ because $g\,q_{\mathrm{out}}$ and $(g\cdot q)_{\mathrm{out}}$ represent the same coset (the sum is finite since $H$ has finite index). The assertion is that this homomorphism coincides with Mathlib's transfer homomorphism `MonoidHom.transfer` applied to $\varphi$ viewed as a homomorphism $H \to \mathrm{Multiplicative}\,A$, the result being transported back along the $\mathrm{Additive}$/$\mathrm{Multiplicative}$ type synonyms. Thus the project's explicit coset-sum corestriction is the classical transfer map.
--
--   This identifies the coset-sum corestriction used in the construction of Hecke operators on group cohomology with the classical transfer (Verlagerung) homomorphism of Schur, so that the library's transfer lemmas become available for it. It is used in the comparison of Hecke operators with their cohomological descriptions and in the level-raising arguments, for instance by [`CohCarrier.heckeT_top_apply_eq_heckeOperatorHom`](thm.html#CohCarrier.heckeT_top_apply_eq_heckeOperatorHom) and [`LevelRaising.exists_parabolicPairings_perfect_mod_three`](thm.html#LevelRaising.exists_parabolicPairings_perfect_mod_three).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_HeckeEis_coresHom_eq_transfer.lean

import Definitions.Def_Gamma0HeckeOperatorHom
import Mathlib.GroupTheory.Transfer

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem HeckeEis.coresHom_eq_transfer {G : Type*} [Group G] (H : Subgroup G) [H.FiniteIndex]
    {A : Type*} [AddCommGroup A] (φ : Additive ↥H →+ A) :
    HeckeEis.coresHom (H := H) φ
      = MonoidHom.toAdditiveLeft
          (MonoidHom.transfer (AddMonoidHom.toMultiplicativeRight φ)) := by sorry
