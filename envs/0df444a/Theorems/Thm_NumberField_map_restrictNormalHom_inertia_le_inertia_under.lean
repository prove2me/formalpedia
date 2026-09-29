-- Prove2me | Theorems.Thm_NumberField_map_restrictNormalHom_inertia_le_inertia_under
-- name    : NumberField.map_restrictNormalHom_inertia_le_inertia_under
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:57.964832+00:00
-- url     : https://prove2.me/theorems/5094e93a-6233-5ddd-ad1f-a7ed6ef29301
-- title:
--   Restriction maps inertia into inertia in a tower
-- statement:
--   Let $E$, $L$, $F$ be number fields equipped with $E$-algebra structures on $L$ and $F$ and an $L$-algebra structure on $F$, compatible as a scalar tower $E \subseteq L \subseteq F$, with $F/E$ Galois and $L/E$ normal, and let $w$ be a height-one prime of the ring of integers $\mathcal{O}_F$. Write $\mathfrak{q} = w \cap \mathcal{O}_L$ for the height-one prime of $\mathcal{O}_L$ obtained by contracting $w$ along $\mathcal{O}_L \to \mathcal{O}_F$. The assertion is an inclusion of subgroups of $\operatorname{Gal}(L/E)$: the image, under the restriction homomorphism $\operatorname{Gal}(F/E) \to \operatorname{Gal}(L/E)$, $\sigma \mapsto \sigma|_L$, of the inertia subgroup of $w$ — that is, of the set of $\sigma$ with $\sigma \cdot x - x \in w$ for all $x \in \mathcal{O}_F$ — is contained in the inertia subgroup of $\mathfrak{q}$ for the action of $\operatorname{Gal}(L/E)$ on $\mathcal{O}_L$, namely the set of $\tau$ with $\tau \cdot y - y \in \mathfrak{q}$ for all $y \in \mathcal{O}_L$. Only the inclusion is claimed, not the surjectivity of restriction onto the inertia subgroup downstairs.
--
--   This is the easy half of the behaviour of inertia subgroups in a tower of normal extensions: an automorphism acting trivially on $\mathcal{O}_F/w$ acts trivially on the subring $\mathcal{O}_L/\mathfrak{q}$. It is used in the ramification/character argument of [`M4aHerbrand.inertia_le_map_unitIdelesTrivialOn_compl_singleton_of_idelicArtinMap`](thm.html#M4aHerbrand.inertia_le_map_unitIdelesTrivialOn_compl_singleton_of_idelicArtinMap).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_NumberField_map_restrictNormalHom_inertia_le_inertia_under.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
open NumberField IsDedekindDomain

theorem NumberField.map_restrictNormalHom_inertia_le_inertia_under
    (E L F : Type) [Field E] [NumberField E] [Field L] [NumberField L] [Field F] [NumberField F]
    [Algebra E L] [Algebra L F] [Algebra E F] [IsScalarTower E L F] [IsGalois E F] [Normal E L]
    (w : HeightOneSpectrum (𝓞 F)) :
    (w.asIdeal.inertia (F ≃ₐ[E] F)).map (AlgEquiv.restrictNormalHom L)
      ≤ (w.under (𝓞 L)).asIdeal.inertia (L ≃ₐ[E] L) := by sorry
