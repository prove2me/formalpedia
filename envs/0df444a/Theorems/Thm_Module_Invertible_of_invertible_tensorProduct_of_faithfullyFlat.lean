-- Prove2me | Theorems.Thm_Module_Invertible_of_invertible_tensorProduct_of_faithfullyFlat
-- name    : Module.Invertible.of_invertible_tensorProduct_of_faithfullyFlat
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:55.610395+00:00
-- url     : https://prove2.me/theorems/c844f4c3-882a-5601-afd8-ed8e45a5f943
-- title:
--   Faithfully flat descent of invertibility of modules
-- statement:
--   Let $R$ be a commutative ring and let $S$ be a commutative ring equipped with an $R$-algebra structure which is faithfully flat as an $R$-module. Let $M$ be an $R$-module (an additive commutative group with an $R$-module structure). Assume that the base change $S \otimes_R M$, viewed as an $S$-module through the left tensor factor, is invertible in the sense of Mathlib's class `Module.Invertible S (TensorProduct R S M)`; this invertibility of the base-changed module is the sole mathematical hypothesis, and it is supplied as an instance. The conclusion is that $M$ itself is an invertible $R$-module, i.e. `Module.Invertible R M` holds. Thus invertibility of a module is detected after a faithfully flat base change: no finiteness, projectivity or rank hypothesis on $M$ is imposed beforehand, these being consequences of the hypothesis on $S \otimes_R M$ together with faithful flatness of $S$ over $R$.
--
--   This is the module-theoretic instance of faithfully flat descent for the property of being invertible, equivalently the statement that the map on objects $\mathrm{Pic}(R) \to \mathrm{Pic}(S)$ reflects invertibility. It is used for the corresponding descent statements for invertible modules on schemes and for local isomorphy of polarisations along faithfully flat base change, and in the analysis of Amitsur cocycles.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Module_Invertible_of_invertible_tensorProduct_of_faithfullyFlat.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

universe u v w

theorem Module.Invertible.of_invertible_tensorProduct_of_faithfullyFlat
    {R : Type u} [CommRing R] (S : Type v) [CommRing S] [Algebra R S] [Module.FaithfullyFlat R S]
    {M : Type w} [AddCommGroup M] [Module R M]
    [Module.Invertible S (TensorProduct R S M)] :
    Module.Invertible R M := by sorry
