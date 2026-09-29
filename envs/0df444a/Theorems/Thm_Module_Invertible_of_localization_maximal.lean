-- Prove2me | Theorems.Thm_Module_Invertible_of_localization_maximal
-- name    : Module.Invertible.of_localization_maximal
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:55.610395+00:00
-- url     : https://prove2.me/theorems/3db92cdf-b643-580f-b4d7-8113c515d06f
-- title:
--   Invertibility of a finitely presented module is local
-- statement:
--   Let $R$ be a commutative ring (in `Type`) and let $M$ be an $R$-module, with $M$ finitely presented as an $R$-module. Assume that for every ideal $P$ of $R$ that is maximal, the localisation `LocalizedModule P.primeCompl M`, i.e. $M_P = M \otimes_R R_P$ obtained by inverting the prime complement of $P$, is an invertible module over the local ring `Localization.AtPrime P` $= R_P$, in Mathlib's sense `Module.Invertible`. The conclusion is that $M$ itself is an invertible $R$-module, `Module.Invertible R M`. Thus invertibility of a finitely presented module is detected at all maximal ideals; no hypothesis beyond finite presentation of $M$ and the family of local invertibility assumptions is imposed.
--
--   This is the standard local–global principle for invertible modules: a finitely presented module is invertible (a line bundle, i.e. a class in $\operatorname{Pic}(R)$) as soon as all its localisations at maximal ideals are. It is used in the construction of invertible quotients of submodules and in the gluing step for the formal $\Omega$ used in the Čerednik–Drinfeld part of the development.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Module_Invertible_of_localization_maximal.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped TensorProduct

theorem Module.Invertible.of_localization_maximal
    {R : Type} [CommRing R] {M : Type} [AddCommGroup M] [Module R M] [Module.FinitePresentation R M]
    (H : ∀ (P : Ideal R) [P.IsMaximal], Module.Invertible (Localization.AtPrime P) (LocalizedModule P.primeCompl M)) :
    Module.Invertible R M := by sorry
