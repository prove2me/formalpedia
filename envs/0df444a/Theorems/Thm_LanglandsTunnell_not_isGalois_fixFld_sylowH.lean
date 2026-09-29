-- Prove2me | Theorems.Thm_LanglandsTunnell_not_isGalois_fixFld_sylowH
-- name    : LanglandsTunnell.not_isGalois_fixFld_sylowH
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:11.015121+00:00
-- url     : https://prove2.me/theorems/050742af-3311-56da-ab44-38681a7b26b3
-- title:
--   The fixed field of `sylowH` is not Galois over ℚ
-- statement:
--   Let $L$ be a type carrying a field structure which is a number field and is Galois over $\mathbb{Q}$, and let $e$ be an isomorphism of groups $\mathrm{Gal}(L/\mathbb{Q}) = (L \simeq_{\mathbb{Q}} L) \to \mathrm{GL}_2(\mathbb{Z}/3)$. Inside $\mathrm{Gal}(L/\mathbb{Q})$ consider the subgroup `sylowH e` consisting of those automorphisms $\gamma$ for which the underlying $2 \times 2$ matrix over $\mathbb{Z}/3$ of $e\gamma$ is the entrywise image under the ring map `red` (a map from $\mathbb{Z}[\sqrt{-2}]$ to $\mathbb{Z}/3$) of some matrix $M$ satisfying the predicate `P16`, a finite explicit collection of matrices over $\mathbb{Z}[\sqrt{-2}]$ containing the identity and closed under products, with each member $M$ having $M$ times its seventh power `pw M 7` again reducing to the identity; these closure properties are what make the set a subgroup. Let `fixFld (sylowH e)` be the intermediate field of $\mathbb{Q} \subseteq L$ fixed pointwise by this subgroup. The assertion is that this intermediate field is not a Galois extension of $\mathbb{Q}$.
--
--   This is the statement that the subfield of $L$ cut out by the distinguished Sylow $2$-subgroup of $\mathrm{GL}_2(\mathbb{F}_3) \cong \mathrm{Gal}(L/\mathbb{Q})$ — here described concretely by reduction modulo a prime above $3$ of sixteen matrices over $\mathbb{Z}[\sqrt{-2}]$ — fails to be normal over $\mathbb{Q}$, equivalently that the subgroup itself is not normal. It is used in the construction underlying the Langlands–Tunnell input, in [`LanglandsTunnell.exists_agreesLiftTraceSeed_isCusp_pair_of_detDictionaryRow_of_coversModCentre`](thm.html#LanglandsTunnell.exists_agreesLiftTraceSeed_isCusp_pair_of_detDictionaryRow_of_coversModCentre).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_not_isGalois_fixFld_sylowH.lean

import Definitions.Def_LanglandsTunnell_QuatH

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem LanglandsTunnell.not_isGalois_fixFld_sylowH {L : Type} [Field L] [NumberField L] [IsGalois ℚ L]
    (e : (L ≃ₐ[ℚ] L) ≃* Matrix.GeneralLinearGroup (Fin 2) (ZMod 3)) :
    ¬ IsGalois ℚ ↥(fixFld (sylowH e)) := by sorry
