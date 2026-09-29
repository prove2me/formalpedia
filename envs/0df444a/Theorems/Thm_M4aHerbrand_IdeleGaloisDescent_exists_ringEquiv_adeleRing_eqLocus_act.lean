-- Prove2me | Theorems.Thm_M4aHerbrand_IdeleGaloisDescent_exists_ringEquiv_adeleRing_eqLocus_act
-- name    : M4aHerbrand.IdeleGaloisDescent.exists_ringEquiv_adeleRing_eqLocus_act
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:11.33382+00:00
-- url     : https://prove2.me/theorems/11a20887-53a1-5230-a2ea-424bb439f30a
-- title:
--   Adeles fixed by σ form the adele ring of the fixed field
-- statement:
--   Let $K$, $L$, $E$ be fields with $L$ and $E$ number fields, $L$ an algebra over $K$ and $L$ an algebra over $E$. Let $\sigma$ be an automorphism of $L$ as a $K$-algebra, and let $D$ be an idele Galois descent datum for $(\mathcal{O}_L, K, L)$, that is: a monoid homomorphism $\mathrm{act}$ from the group of $K$-algebra automorphisms of $L$ to the group of ring automorphisms of the adele ring $\mathbb{A}_L =$ `AdeleRing (𝓞 L) L`, such that for every automorphism $g$ and every $x \in L$ the automorphism $\mathrm{act}(g)$ sends the principal adele of $x$ to the principal adele of $g(x)$, and such that each $\mathrm{act}(g)$ is continuous. Assume $E$ realises the fixed field of $\sigma$ in the sense that an element $x \in L$ satisfies $\sigma x = x$ if and only if $x$ lies in the image of the structure map $E \to L$. The conclusion asserts the existence of a ring isomorphism $e$ from the adele ring $\mathbb{A}_E =$ `AdeleRing (𝓞 E) E` onto the subring of $\mathbb{A}_L$ on which the ring homomorphism underlying $D.\mathrm{act}(\sigma)$ agrees with the identity, i.e. the subring of adeles of $L$ fixed by $D.\mathrm{act}(\sigma)$, which is compatible with principal adeles: for every $a \in E$, the element $e$ applied to the principal adele of $a$ in $\mathbb{A}_E$, viewed inside $\mathbb{A}_L$, equals the principal adele of the image of $a$ in $L$. Only existence of such an isomorphism of rings is asserted; no continuity or topological statement about $e$ is made.
--
--   This is the adelic form of Galois descent for a cyclic extension: the $\sigma$-invariants of $\mathbb{A}_L$ are the adeles of the fixed field $E$, compatibly with principal adeles. It is used in the study of the adelic action on automorphic forms, being cited by [`AutomorphicForm.exists_eq_inv_mul_sigmaAdelicAct_of_prod_sigmaAdelicAct_pow_eq_one`](thm.html#AutomorphicForm.exists_eq_inv_mul_sigmaAdelicAct_of_prod_sigmaAdelicAct_pow_eq_one).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_M4aHerbrand_IdeleGaloisDescent_exists_ringEquiv_adeleRing_eqLocus_act.lean

import Definitions.Def_M4aHerbrand_IdeleClassVocab

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open NumberField

theorem M4aHerbrand.IdeleGaloisDescent.exists_ringEquiv_adeleRing_eqLocus_act
    (K L E : Type) [Field K] [Field L] [NumberField L] [Algebra K L]
    [Field E] [NumberField E] [Algebra E L]
    (σ : L ≃ₐ[K] L) (D : M4aHerbrand.IdeleGaloisDescent (𝓞 L) K L)
    (hE : ∀ x : L, σ x = x ↔ x ∈ Set.range (algebraMap E L)) :
    ∃ e : (AdeleRing (𝓞 E) E ≃+*
        RingHom.eqLocus ((D.act σ : RingAut (AdeleRing (𝓞 L) L)).toRingHom) (RingHom.id (AdeleRing (𝓞 L) L))),
      ∀ a : E, (e (algebraMap E (AdeleRing (𝓞 E) E) a) : AdeleRing (𝓞 L) L) =
        algebraMap L (AdeleRing (𝓞 L) L) (algebraMap E L a) := by sorry
