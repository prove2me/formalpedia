-- Prove2me | Theorems.Thm_M4aHerbrand_IdeleGaloisDescent_exists_ringEquiv_prod_forall_act_eq
-- name    : M4aHerbrand.IdeleGaloisDescent.exists_ringEquiv_prod_forall_act_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:11.33382+00:00
-- url     : https://prove2.me/theorems/c46846e2-62da-5416-a661-5e3e3c5efb20
-- title:
--   Galois action on adeles splits into archimedean and finite parts
-- statement:
--   Let $K$ and $L$ be number fields with $L$ an algebra over $K$ such that $L/K$ is Galois, let $D$ be an idele Galois descent datum for $\mathcal{O}_L$ over the pair $(K,L)$ — that is, a monoid homomorphism $D.\mathrm{act}$ from the group $L \simeq_{\mathrm{alg}[K]} L$ of $K$-algebra automorphisms of $L$ to the group of ring automorphisms of the adele ring $\mathbb{A}_L =$ `AdeleRing (𝓞 L) L`, subject to the two conditions that $D.\mathrm{act}\,g$ commutes with the structure map $L \to \mathbb{A}_L$ in the sense that $D.\mathrm{act}\,g\,(\iota(x)) = \iota(g x)$ for all $g$ and all $x \in L$, and that $D.\mathrm{act}\,g$ is continuous for every $g$ — and let $\sigma$ be a $K$-algebra automorphism of $L$. Then there exist a ring isomorphism $A$ of the infinite adele ring `InfiniteAdeleRing L` with itself and a ring isomorphism $B$ of the finite adele ring `FiniteAdeleRing (𝓞 L) L` with itself, both continuous, such that for every adele $x \in \mathbb{A}_L$ — an adele being by definition a pair consisting of an infinite and a finite component — one has $D.\mathrm{act}\,\sigma\,(x) = (A\,x_\infty, B\,x_f)$.
--
--   This records that the Galois action on the adeles of $L$ respects the decomposition $\mathbb{A}_L = \mathbb{A}_{L,\infty} \times \mathbb{A}_{L,f}$, acting through a continuous ring automorphism of each factor separately. It is used where archimedean factors of $\sigma$-twisted adelic integrands must be seen to depend on the archimedean variables alone, in particular in the factorisation of orbital integrals for automorphic forms.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_M4aHerbrand_IdeleGaloisDescent_exists_ringEquiv_prod_forall_act_eq.lean

import Definitions.Def_M4aHerbrand_IdeleClassVocab
import Definitions.Def_M4aHerbrand_GenuineDescent

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open NumberField IsDedekindDomain

theorem M4aHerbrand.IdeleGaloisDescent.exists_ringEquiv_prod_forall_act_eq
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] [IsGalois K L]
    (D : M4aHerbrand.IdeleGaloisDescent (𝓞 L) K L) (σ : L ≃ₐ[K] L) :
    ∃ (A : InfiniteAdeleRing L ≃+* InfiniteAdeleRing L) (B : FiniteAdeleRing (𝓞 L) L ≃+* FiniteAdeleRing (𝓞 L) L),
      Continuous A ∧ Continuous B ∧
      ∀ x : AdeleRing (𝓞 L) L, (D.act σ : RingAut (AdeleRing (𝓞 L) L)) x = (A x.1, B x.2) := by sorry
