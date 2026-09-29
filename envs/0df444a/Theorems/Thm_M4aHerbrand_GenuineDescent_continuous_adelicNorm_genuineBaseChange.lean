-- Prove2me | Theorems.Thm_M4aHerbrand_GenuineDescent_continuous_adelicNorm_genuineBaseChange
-- name    : M4aHerbrand.GenuineDescent.continuous_adelicNorm_genuineBaseChange
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:11.33382+00:00
-- url     : https://prove2.me/theorems/e4665560-7ad9-5c8a-b7ca-4e87aa901889
-- title:
--   Continuity of the adelic norm A_M → A_K
-- statement:
--   Let $K$ and $M$ be number fields (types in `Type` carrying field and `NumberField` instances) and suppose $M$ is a $K$-algebra. The term `genuineBaseChange K M` is the base-change datum `AdeleBaseChange (𝓞 K) K (𝓞 M) M` assembled from `genuineβ K M`, namely: a ring homomorphism $\beta \colon \mathbb{A}_K \to \mathbb{A}_M$ between the adele rings of $K$ and of $M$, the compatibility $\beta(\iota_K(x)) = \iota_M(\mathrm{alg}_{K\to M}(x))$ for all $x \in K$ with the canonical maps of the fields into their adele rings, together with the isomorphism `genuineTensorEquiv K M` of $\mathbb{A}_K$-algebras $\mathbb{A}_K \otimes_K M \cong \mathbb{A}_M$ (the $\mathbb{A}_K$-structure on $\mathbb{A}_M$ being the one induced by $\beta$), which sends $1 \otimes m$ to the image of $m$ in $\mathbb{A}_M$ for every $m \in M$. Its `adelicNorm` is the algebra norm of $\mathbb{A}_M$ over $\mathbb{A}_K$ for that structure, a monoid homomorphism $\mathbb{A}_M \to^{*} \mathbb{A}_K$. The assertion is that the underlying function of this norm map is continuous for the adelic topologies on $\mathbb{A}_M$ and $\mathbb{A}_K$.
--
--   This is the continuity of the norm map $N_{M/K}$ on adeles, as in Weil's treatment of the adelic norm. It is used throughout the automorphic part of the development, where base change of characters and of automorphic data along $N_{M/K}$ must be known to preserve continuity.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_M4aHerbrand_GenuineDescent_continuous_adelicNorm_genuineBaseChange.lean

import Mathlib
import Definitions.Def_M4aHerbrand_GenuineDescent

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open NumberField M4aHerbrand.GenuineDescent

theorem M4aHerbrand.GenuineDescent.continuous_adelicNorm_genuineBaseChange
    (K M : Type) [Field K] [NumberField K] [Field M] [NumberField M] [Algebra K M] :
    Continuous (genuineBaseChange K M).adelicNorm := by sorry
