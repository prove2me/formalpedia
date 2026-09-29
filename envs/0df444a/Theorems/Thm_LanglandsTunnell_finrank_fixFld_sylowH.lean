-- Prove2me | Theorems.Thm_LanglandsTunnell_finrank_fixFld_sylowH
-- name    : LanglandsTunnell.finrank_fixFld_sylowH
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:10.196979+00:00
-- url     : https://prove2.me/theorems/44b3bb28-5908-51ef-a644-50e3a4dc8c10
-- title:
--   The fixed field of `sylowH` is cubic over ℚ
-- statement:
--   Let $L$ be a number field, taken in the smallest universe, which is Galois over $\mathbb{Q}$, and let $e$ be a group isomorphism from the group $L \simeq_{\mathbb{Q}}^{\mathrm{alg}} L$ of $\mathbb{Q}$-algebra automorphisms of $L$ onto $\mathrm{GL}_2(\mathbb{Z}/3)$. Let `sylowH e` be the subgroup of $L \simeq_{\mathbb{Q}}^{\mathrm{alg}} L$ consisting of those automorphisms $\gamma$ for which the matrix underlying $e(\gamma)$ is the entrywise reduction, along the ring map `red`, of some matrix belonging to the explicit finite set `P16` (the subgroup axioms being witnessed by `one_mem_P16`, the multiplicative closure `P16_mul_closed` of `P16`, and `P16_mul_pw_seven`, which produces an inverse inside `P16` as a seventh power). Write `fixFld (sylowH e)` for the intermediate field of $L/\mathbb{Q}$ consisting of the elements of $L$ fixed by every automorphism in `sylowH e`. The assertion is that this intermediate field has dimension exactly $3$ as a $\mathbb{Q}$-vector space, i.e. it is a cubic subfield of $L$.
--
--   This is the elementary Galois-theoretic degree count underlying the cubic field used for non-normal base change in the Langlands–Tunnell input to the argument: in an octahedral tower $L/\mathbb{Q}$ with group identified with $\mathrm{GL}_2(\mathbb{F}_3)$, the fixed field of the distinguished $2$-subgroup singled out by `sylowH` is cubic. It is cited by [`LanglandsTunnell.exists_agreesFormalBaseChange_arithGenuineCuspRealizable_sylowH_of_quatH_of_unitary_resolvent`](thm.html#LanglandsTunnell.exists_agreesFormalBaseChange_arithGenuineCuspRealizable_sylowH_of_quatH_of_unitary_resolvent).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_finrank_fixFld_sylowH.lean

import Definitions.Def_LanglandsTunnell_C8Tower

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open NumberField LanglandsTunnell

theorem LanglandsTunnell.finrank_fixFld_sylowH {L : Type} [Field L] [NumberField L] [IsGalois ℚ L]
    (e : (L ≃ₐ[ℚ] L) ≃* Matrix.GeneralLinearGroup (Fin 2) (ZMod 3)) :
    Module.finrank ℚ ↥(fixFld (sylowH e)) = 3 := by sorry
