-- Prove2me | Theorems.Thm_M4aHerbrand_adeleBaseChange_local_rigidity
-- name    : M4aHerbrand.adeleBaseChange_local_rigidity
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:11.33382+00:00
-- url     : https://prove2.me/theorems/a5157a85-b19f-5acf-bd2a-f1e95289dda6
-- title:
--   Local rigidity of adele base-change data
-- statement:
--   Let $K$ and $L$ be number fields, with $L$ an algebra over $K$, and let $B$ be an adele base-change datum for the pair $(\mathcal{O}_K,K)$, $(\mathcal{O}_L,L)$: that is, a ring homomorphism $\beta \colon \mathbb{A}_K \to \mathbb{A}_L$ between the adele rings, compatible with the principal embeddings in the sense that $\beta(\iota_K(e)) = \iota_L(e_L)$ for every $e \in K$ (where $e_L$ is the image of $e$ in $L$), together with an isomorphism $\mathbb{A}_K \otimes_K L \cong \mathbb{A}_L$ of $\mathbb{A}_K$-algebras for the $\mathbb{A}_K$-algebra structure on $\mathbb{A}_L$ given by $\beta$, sending $1 \otimes f$ to $\iota_L(f)$ for all $f \in L$. The conclusion is a conjunction. First, for every adele $a \in \mathbb{A}_K$ and every nonzero prime $w$ of $\mathcal{O}_L$, the $w$-component of the finite part of $\beta(a)$ equals the image of the $w \cap \mathcal{O}_K$-component of the finite part of $a$ under `HeightOneSpectrum.Extension.adicCompletionSemialgHom`, the canonical map $K_{w \cap \mathcal{O}_K} \to L_w$ of adic completions semilinear over $K \to L$, applied to $w$ viewed as an extension of $w \cap \mathcal{O}_K$. Second, for every infinite place $w$ of $L$ there are an infinite place $v$ of $K$ and a ring automorphism $\theta$ of $\mathbb{C}$ such that for all $a \in \mathbb{A}_K$, reading the $w$-component of the infinite part of $\beta(a)$ and the $v$-component of the infinite part of $a$ inside $\mathbb{C}$ through the embeddings `InfinitePlace.Completion.extensionEmbedding`, the former is $\theta$ of the latter. Note that $\theta$ is only assumed to be a ring automorphism, not a continuous one, and that $w$ is not asserted to lie above $v$.
--
--   This is the rigidity statement for adele base-change data: the finite components of any such $\beta$ are forced to be the canonical maps $K_v \to L_w$ on completions, while the archimedean components are pinned down only up to an abstract automorphism of $\mathbb{C}$. It is used in the componentwise analysis of idelic norms and in the identification of the image of the idelic norm map.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_M4aHerbrand_adeleBaseChange_local_rigidity.lean

import Definitions.Def_M4aHerbrand_AdeleBaseChange
import Definitions.Def_DedekindDomain_Completion_BaseChange

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
open NumberField IsDedekindDomain M4aHerbrand

theorem M4aHerbrand.adeleBaseChange_local_rigidity
    (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (B : AdeleBaseChange (𝓞 K) K (𝓞 L) L) :
    (∀ (a : AdeleRing (𝓞 K) K) (w : HeightOneSpectrum (𝓞 L)),
      ((B.β a).2 : FiniteAdeleRing (𝓞 L) L) w =
        HeightOneSpectrum.Extension.adicCompletionSemialgHom K L
          (⟨w, rfl⟩ : (w.under (𝓞 K)).Extension (𝓞 L))
          ((a.2 : FiniteAdeleRing (𝓞 K) K) (w.under (𝓞 K)))) ∧
    ∀ w : InfinitePlace L, ∃ (v : InfinitePlace K) (θ : ℂ ≃+* ℂ), ∀ a : AdeleRing (𝓞 K) K,
      InfinitePlace.Completion.extensionEmbedding w (((B.β a).1 : InfiniteAdeleRing L) w) =
        θ (InfinitePlace.Completion.extensionEmbedding v ((a.1 : InfiniteAdeleRing K) v)) := by sorry
