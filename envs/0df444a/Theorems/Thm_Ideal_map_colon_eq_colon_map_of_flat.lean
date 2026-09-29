-- Prove2me | Theorems.Thm_Ideal_map_colon_eq_colon_map_of_flat
-- name    : Ideal.map_colon_eq_colon_map_of_flat
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:57.239308+00:00
-- url     : https://prove2.me/theorems/78fde7dd-b7db-5609-bc73-82a5e7fe3a7c
-- title:
--   Flat base change for colon ideals of finitely generated ideals
-- statement:
--   Let $R$ and $S$ be commutative rings with an $R$-algebra structure on $S$ for which $S$ is flat as an $R$-module, and let $I$ and $J$ be ideals of $R$ with $J$ finitely generated (the hypothesis `J.FG`). The assertion is an equality of ideals of $S$: the image under $\operatorname{algebraMap} R S$ of the colon ideal $\mathrm{colon}(I, J) = \{r \in R \mid r \cdot J \subseteq I\}$, extended to an ideal of $S$ by `Ideal.map`, coincides with the colon ideal of the extended ideal $I S = I.\mathrm{map}(\operatorname{algebraMap} R S)$ with respect to the underlying set of the extended ideal $J S = J.\mathrm{map}(\operatorname{algebraMap} R S)$, i.e. with $\{s \in S \mid s \cdot (JS) \subseteq IS\}$. In Mathlib's formulation the second argument of `Submodule.colon` is a set, taken here to be the carrier of $J$ on the left and the carrier of $JS$ on the right; thus the statement is $(I : J)\,S = (IS : JS)$, with finite generation assumed of $J$ only.
--
--   This is the standard compatibility of ideal quotients (colon ideals) with flat base change, valid for a finitely generated second argument. It is used in the study of adic completions of local rings, where $S$ is the completion of a noetherian local ring $R$ and hence $R$-flat, in [`IsLocalRing.exists_crossingPresentation_of_ringEquiv_adicCompletion_uvCrossingModel`](thm.html#IsLocalRing.exists_crossingPresentation_of_ringEquiv_adicCompletion_uvCrossingModel).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Ideal_map_colon_eq_colon_map_of_flat.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem Ideal.map_colon_eq_colon_map_of_flat
    {R S : Type*} [CommRing R] [CommRing S] [Algebra R S] [Module.Flat R S]
    (I J : Ideal R) (hJ : J.FG) :
    (Submodule.colon I (J : Set R)).map (algebraMap R S)
      = Submodule.colon (I.map (algebraMap R S)) (J.map (algebraMap R S) : Set S) := by sorry
