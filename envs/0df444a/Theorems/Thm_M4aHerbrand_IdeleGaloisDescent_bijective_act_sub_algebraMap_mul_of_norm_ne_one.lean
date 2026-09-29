-- Prove2me | Theorems.Thm_M4aHerbrand_IdeleGaloisDescent_bijective_act_sub_algebraMap_mul_of_norm_ne_one
-- name    : M4aHerbrand.IdeleGaloisDescent.bijective_act_sub_algebraMap_mul_of_norm_ne_one
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:11.33382+00:00
-- url     : https://prove2.me/theorems/f67a4b68-cafe-52a7-8569-e99979ae21b4
-- title:
--   Bijectivity of s ↦ σ(s) - cs on adeles
-- statement:
--   Let $R$ be a Dedekind domain, $E$ and $F$ fields with $F$ the fraction field of $R$ (via a given $R$-algebra structure on $F$), and let $F$ be a finite Galois extension of $E$. Let $D$ be an idele Galois descent datum for $R$, $E$, $F$: that is, a monoid homomorphism $\mathrm{act}$ from $\mathrm{Gal}(F/E) = F \simeq_{\mathrm{alg}[E]} F$ to the group of ring automorphisms of the adele ring $\mathbb{A} =$ `AdeleRing R F`, such that for every $g$ in the Galois group and every $x \in F$ one has $\mathrm{act}(g)$ applied to the principal adele of $x$ equal to the principal adele of $g(x)$, and such that each $\mathrm{act}(g)$ is continuous. Let $\sigma$ be an $E$-algebra automorphism of $F$ such that every $\tau \in \mathrm{Gal}(F/E)$ lies in the subgroup of integer powers of $\sigma$, so that the Galois group is cyclic with generator $\sigma$. Let $c \in F$ satisfy $N_{F/E}(c) \neq 1$, where $N_{F/E}$ is the algebra norm of $F$ over $E$. Then the map $\mathbb{A} \to \mathbb{A}$ sending $s$ to $D.\mathrm{act}(\sigma)(s) - \iota(c)\, s$, with $\iota$ the canonical map $F \to \mathbb{A}$, is bijective.
--
--   This is the adelic form of the bijectivity statement used in Langlands's base-change comparison (Lemma 4.5 of *Base Change for GL(2)*): the twisted difference operator $s \mapsto \sigma(s) - cs$ on the adeles is invertible as soon as the norm of the twisting constant is not $1$. It is invoked in the unfolding of constant terms of automorphic forms, where the substitution $u(s) \mapsto \delta^{-1}u(s)^{-1}\delta\,\sigma(u(s))$ on adelic unipotent matrices is governed by this map, and it underlies the refinement producing a measure-preserving continuous additive equivalence.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_M4aHerbrand_IdeleGaloisDescent_bijective_act_sub_algebraMap_mul_of_norm_ne_one.lean

import Definitions.Def_M4aHerbrand_IdeleClassVocab
import Mathlib.RingTheory.Norm.Basic

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open NumberField

theorem M4aHerbrand.IdeleGaloisDescent.bijective_act_sub_algebraMap_mul_of_norm_ne_one
    {R E F : Type*} [CommRing R] [IsDedekindDomain R] [Field E] [Field F]
    [Algebra R F] [IsFractionRing R F] [Algebra E F] [FiniteDimensional E F] [IsGalois E F]
    (D : M4aHerbrand.IdeleGaloisDescent R E F)
    {σ : F ≃ₐ[E] F} (hgen : ∀ τ : F ≃ₐ[E] F, τ ∈ Subgroup.zpowers σ)
    (c : F) (hc : Algebra.norm E c ≠ 1) :
    Function.Bijective fun s : AdeleRing R F =>
      (D.act σ : RingAut (AdeleRing R F)) s - algebraMap F (AdeleRing R F) c * s := by sorry
