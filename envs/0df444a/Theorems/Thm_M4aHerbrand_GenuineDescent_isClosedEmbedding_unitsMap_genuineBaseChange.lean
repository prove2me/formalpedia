-- Prove2me | Theorems.Thm_M4aHerbrand_GenuineDescent_isClosedEmbedding_unitsMap_genuineBaseChange
-- name    : M4aHerbrand.GenuineDescent.isClosedEmbedding_unitsMap_genuineBaseChange
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:11.33382+00:00
-- url     : https://prove2.me/theorems/1a3d9995-ff81-502b-90b0-8f7f5b8ed418
-- title:
--   Adelic base change is a closed embedding on ideles
-- statement:
--   Let $K$ and $L$ be fields that are number fields, with $L$ given as a $K$-algebra (so the structure map $K \to L$ is a finite extension of number fields). Attached to this datum is the object [`M4aHerbrand.GenuineDescent.genuineBaseChange K L`](def/M4aHerbrand_GenuineDescent.html#L87), an instance of the structure `AdeleBaseChange` for $(\mathcal{O}_K,K)$ and $(\mathcal{O}_L,L)$: that is, a ring homomorphism $\beta \colon \mathbb{A}_K \to \mathbb{A}_L$ between the adele rings, satisfying $\beta(\iota_K(e)) = \iota_L(e_L)$ for every $e \in K$ (where $\iota$ denotes the diagonal embeddings and $e_L$ the image of $e$ in $L$), together with an isomorphism of $\mathbb{A}_K$-algebras $\mathbb{A}_K \otimes_K L \xrightarrow{\sim} \mathbb{A}_L$ (for the $\mathbb{A}_K$-algebra structure on $\mathbb{A}_L$ induced by $\beta$) which carries $1 \otimes f$ to $\iota_L(f)$ for every $f \in L$. The assertion is that the induced map on unit groups, $\beta^{\times} \colon \mathbb{A}_K^{\times} \to \mathbb{A}_L^{\times}$, obtained by applying `Units.map` to the underlying multiplicative homomorphism of $\beta$, is a closed topological embedding: it is injective, a homeomorphism onto its image, and its image is closed in the idele group $\mathbb{A}_L^{\times}$.
--
--   This is the topological input needed to regard the idele group of $K$ as a closed subgroup of the idele group of $L$ along adelic base change, so that quotients, transported Haar measures and fixed-point descriptions of the image make sense. It is used in the automorphic-form layer, in particular in identifying the image of the principal/norm-power construction with a fixed set of $\beta^{\times}$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_M4aHerbrand_GenuineDescent_isClosedEmbedding_unitsMap_genuineBaseChange.lean

import Definitions.Def_M4aHerbrand_GenuineDescent

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open NumberField

theorem M4aHerbrand.GenuineDescent.isClosedEmbedding_unitsMap_genuineBaseChange
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] :
    Topology.IsClosedEmbedding
      (Units.map (M4aHerbrand.GenuineDescent.genuineBaseChange K L).β.toMonoidHom :
        (AdeleRing (𝓞 K) K)ˣ → (AdeleRing (𝓞 L) L)ˣ) := by sorry
