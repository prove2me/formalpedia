-- Prove2me | Theorems.Thm_IsLocalRing_exists_trivSqZeroExt_forall_exists_algHom_dualNumber_of_forall_pullback_surjective_of_tangent_injective
-- name    : IsLocalRing.exists_trivSqZeroExt_forall_exists_algHom_dualNumber_of_forall_pullback_surjective_of_tangent_injective
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:59.02392+00:00
-- url     : https://prove2.me/theorems/6804a32d-14eb-5f28-b97a-c4084870bf59
-- title:
--   A universal first-order class over k⊕ kᵈ (Schlessinger)
-- statement:
--   Let $O$ be a commutative local ring with residue field $k=\mathrm{ResidueField}\,O$, and let $F$ assign to every commutative $O$-algebra $A$ together with a ring homomorphism $\mathrm{res}_A\colon A\to k$ a type $F(A,\mathrm{res}_A)$, equipped with a relation $\mathrm{Frel}$ assumed reflexive, symmetric and transitive on each such type, and with a pushforward $\mathrm{Fmap}$ along every $O$-algebra map $f\colon A\to A'$ satisfying $\mathrm{res}_{A'}\circ f=\mathrm{res}_A$, which is assumed to preserve $\mathrm{Frel}$, to send the identity to a $\mathrm{Frel}$-equivalent element, and to take a composite $g\circ f$ to something $\mathrm{Frel}$-equivalent to the iterated pushforward. Assume further: an element $x_0\in F(k,\mathrm{id})$ to which every element of $F(k,\mathrm{id})$ is $\mathrm{Frel}$-related (so $F(k)$ has exactly one class); a gluing hypothesis, for all Artinian local $O$-algebras $B,A',A'',A$ with surjective residue maps to $k$ compatible with $\mathrm{residue}\,O$ and $O$-algebra maps $p'\colon B\to A'$, $p''\colon B\to A''$, $q'\colon A'\to A$, $q''\colon A''\to A$ compatible with these residue maps, with $q'\circ p'=q''\circ p''$, with the element-wise unique-pullback property (for all $a',a''$ with $q'a'=q''a''$ there is a unique $b$ with $p'b=a'$, $p''b=a''$) and with $q''$ surjective: any $x'\in F(A')$ and $x''\in F(A'')$ whose pushforwards to $F(A)$ are $\mathrm{Frel}$-related arise, up to $\mathrm{Frel}$, from a single $y\in F(B)$; and a tangent-space hypothesis consisting of $r\in\mathbb N$ and a map $e\colon F(k[\varepsilon])\to k^r$ (on the dual numbers over $k$, with residue map the first-coordinate homomorphism $\mathrm{TrivSqZeroExt.fstHom}$) which is constant on $\mathrm{Frel}$-classes and injective modulo $\mathrm{Frel}$, is homogeneous for every $O$-algebra endomorphism $\mu$ of $k[\varepsilon]$ over $k$ with $\mathrm{snd}(\mu t)=c\,\mathrm{snd}(t)$ (then $e(\mathrm{Fmap}\,\mu\,x)=c\cdot e(x)$), and is additive in the following sense: for every Artinian local $O$-algebra $B$ with surjective residue map compatible with $\mathrm{residue}\,O$ and all $O$-algebra maps $p_1,p_2,\sigma\colon B\to k[\varepsilon]$ over $\mathrm{res}_B$ such that $(p_1,p_2)$ is jointly injective and jointly surjective onto pairs of dual numbers with equal first components, and $\mathrm{snd}(\sigma b)=\mathrm{snd}(p_1b)+\mathrm{snd}(p_2b)$, one has $e(\mathrm{Fmap}\,\sigma\,y)=e(\mathrm{Fmap}\,p_1\,y)+e(\mathrm{Fmap}\,p_2\,y)$ for all $y\in F(B)$. The conclusion is that there exist $d\in\mathbb N$ and an element $\xi$ of $F$ at the trivial square-zero extension $k\oplus k^d$ (with residue map the first-coordinate homomorphism) such that every $x\in F(k[\varepsilon])$ is $\mathrm{Frel}$-related to $\mathrm{Fmap}\,\theta\,\xi$ for some $O$-algebra map $\theta\colon k\oplus k^d\to k[\varepsilon]$ over $k$, and such that $\mathrm{Frel}(\mathrm{Fmap}\,\theta\,\xi,\mathrm{Fmap}\,\theta'\,\xi)$ forces $\theta=\theta'$.
--
--   This is the first-order step in Schlessinger's construction of a hull: under the gluing axiom and finiteness of the tangent space, the classes over $k[\varepsilon]$ are parametrised bijectively by the $O$-algebra maps $k\oplus k^d\to k[\varepsilon]$ over $k$ applied to a single class $\xi$ over $k\oplus k^d$, where $d$ is the dimension of the tangent space. It is used by [`IsLocalRing.exists_hull_of_forall_pullback_surjective_of_tangent_injective`](thm.html#IsLocalRing.exists_hull_of_forall_pullback_surjective_of_tangent_injective), which assembles the hull of a deformation functor by successive small extensions.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_IsLocalRing_exists_trivSqZeroExt_forall_exists_algHom_dualNumber_of_forall_pullback_surjective_of_tangent_injective.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open IsLocalRing in

theorem IsLocalRing.exists_trivSqZeroExt_forall_exists_algHom_dualNumber_of_forall_pullback_surjective_of_tangent_injective
    (O : Type u) [CommRing O] [IsLocalRing O]
    (F : ∀ (A : Type u) [CommRing A] [Algebra O A], (A →+* ResidueField O) → Type u)
    (Frel : ∀ {A : Type u} [CommRing A] [Algebra O A] {resA : A →+* ResidueField O},
      F A resA → F A resA → Prop)
    (hrefl : ∀ {A : Type u} [CommRing A] [Algebra O A] {resA : A →+* ResidueField O}
      (x : F A resA), Frel x x)
    (hsymm : ∀ {A : Type u} [CommRing A] [Algebra O A] {resA : A →+* ResidueField O}
      (x y : F A resA), Frel x y → Frel y x)
    (htrans : ∀ {A : Type u} [CommRing A] [Algebra O A] {resA : A →+* ResidueField O}
      (x y z : F A resA), Frel x y → Frel y z → Frel x z)
    (Fmap : ∀ {A : Type u} [CommRing A] [Algebra O A] {resA : A →+* ResidueField O}
      {A' : Type u} [CommRing A'] [Algebra O A'] {resA' : A' →+* ResidueField O}
      (f : A →ₐ[O] A'), resA'.comp f.toRingHom = resA → F A resA → F A' resA')
    (Fmap_rel : ∀ {A : Type u} [CommRing A] [Algebra O A] {resA : A →+* ResidueField O}
      {A' : Type u} [CommRing A'] [Algebra O A'] {resA' : A' →+* ResidueField O}
      (f : A →ₐ[O] A') (hf : resA'.comp f.toRingHom = resA) (x y : F A resA),
      Frel x y → Frel (Fmap f hf x) (Fmap f hf y))
    (Fmap_id : ∀ {A : Type u} [CommRing A] [Algebra O A] {resA : A →+* ResidueField O}
      (h : resA.comp (AlgHom.id O A).toRingHom = resA) (x : F A resA), Frel (Fmap (AlgHom.id O A) h x) x)
    (Fmap_comp : ∀ {A : Type u} [CommRing A] [Algebra O A] {resA : A →+* ResidueField O}
      {A' : Type u} [CommRing A'] [Algebra O A'] {resA' : A' →+* ResidueField O}
      {A'' : Type u} [CommRing A''] [Algebra O A''] {resA'' : A'' →+* ResidueField O}
      (f : A →ₐ[O] A') (g : A' →ₐ[O] A'') (hf : resA'.comp f.toRingHom = resA)
      (hg : resA''.comp g.toRingHom = resA') (hgf : resA''.comp (g.comp f).toRingHom = resA)
      (x : F A resA), Frel (Fmap (g.comp f) hgf x) (Fmap g hg (Fmap f hf x)))

    (x₀ : F (ResidueField O) (RingHom.id (ResidueField O)))
    (hx₀ : ∀ x : F (ResidueField O) (RingHom.id (ResidueField O)), Frel x x₀)

    (hglue : ∀ (B : Type u) [CommRing B] [IsLocalRing B] [IsArtinianRing B] [Algebra O B]
        (resB : B →+* ResidueField O), Function.Surjective resB →
        resB.comp (algebraMap O B) = residue O →
      ∀ (A' : Type u) [CommRing A'] [IsLocalRing A'] [IsArtinianRing A'] [Algebra O A']
        (resA' : A' →+* ResidueField O), Function.Surjective resA' →
        resA'.comp (algebraMap O A') = residue O →
      ∀ (A'' : Type u) [CommRing A''] [IsLocalRing A''] [IsArtinianRing A''] [Algebra O A'']
        (resA'' : A'' →+* ResidueField O), Function.Surjective resA'' →
        resA''.comp (algebraMap O A'') = residue O →
      ∀ (A : Type u) [CommRing A] [IsLocalRing A] [IsArtinianRing A] [Algebra O A]
        (resA : A →+* ResidueField O), Function.Surjective resA →
        resA.comp (algebraMap O A) = residue O →
      ∀ (p' : B →ₐ[O] A') (hp' : resA'.comp p'.toRingHom = resB)
        (p'' : B →ₐ[O] A'') (hp'' : resA''.comp p''.toRingHom = resB)
        (q' : A' →ₐ[O] A) (hq' : resA.comp q'.toRingHom = resA')
        (q'' : A'' →ₐ[O] A) (hq'' : resA.comp q''.toRingHom = resA''),
        q'.comp p' = q''.comp p'' →
        (∀ (a' : A') (a'' : A''), q' a' = q'' a'' → ∃! b : B, p' b = a' ∧ p'' b = a'') →
        Function.Surjective q'' →
        ∀ (x' : F A' resA') (x'' : F A'' resA''), Frel (Fmap q' hq' x') (Fmap q'' hq'' x'') →
          ∃ y : F B resB, Frel (Fmap p' hp' y) x' ∧ Frel (Fmap p'' hp'' y) x'')

    (r : ℕ)
    (e : F (DualNumber (ResidueField O))
        (TrivSqZeroExt.fstHom O (ResidueField O) (ResidueField O)).toRingHom → (Fin r → ResidueField O))
    (he_rel : ∀ x y, Frel x y → e x = e y)
    (he_inj : ∀ x y, e x = e y → Frel x y)
    (he_smul : ∀ (c : ResidueField O)
        (μ : DualNumber (ResidueField O) →ₐ[O] DualNumber (ResidueField O))
        (hμ : (TrivSqZeroExt.fstHom O (ResidueField O) (ResidueField O)).toRingHom.comp μ.toRingHom =
          (TrivSqZeroExt.fstHom O (ResidueField O) (ResidueField O)).toRingHom),
        (∀ t, TrivSqZeroExt.snd (μ t) = c * TrivSqZeroExt.snd t) →
        ∀ x, e (Fmap μ hμ x) = c • e x)
    (he_add : ∀ (B : Type u) [CommRing B] [IsLocalRing B] [IsArtinianRing B] [Algebra O B]
        (resB : B →+* ResidueField O), Function.Surjective resB →
        resB.comp (algebraMap O B) = residue O →
        ∀ (p₁ p₂ σ : B →ₐ[O] DualNumber (ResidueField O))
          (hp₁ : (TrivSqZeroExt.fstHom O (ResidueField O) (ResidueField O)).toRingHom.comp
            p₁.toRingHom = resB)
          (hp₂ : (TrivSqZeroExt.fstHom O (ResidueField O) (ResidueField O)).toRingHom.comp
            p₂.toRingHom = resB)
          (hσ : (TrivSqZeroExt.fstHom O (ResidueField O) (ResidueField O)).toRingHom.comp
            σ.toRingHom = resB),
        (∀ b₁ b₂ : B, p₁ b₁ = p₁ b₂ → p₂ b₁ = p₂ b₂ → b₁ = b₂) →
        (∀ t₁ t₂ : DualNumber (ResidueField O), TrivSqZeroExt.fst t₁ = TrivSqZeroExt.fst t₂ →
            ∃ b : B, p₁ b = t₁ ∧ p₂ b = t₂) →
        (∀ b : B, TrivSqZeroExt.snd (σ b) = TrivSqZeroExt.snd (p₁ b) + TrivSqZeroExt.snd (p₂ b)) →
        ∀ y : F B resB, e (Fmap σ hσ y) = e (Fmap p₁ hp₁ y) + e (Fmap p₂ hp₂ y)) :
    ∃ (d : ℕ) (ξ : F (TrivSqZeroExt (ResidueField O) (Fin d → ResidueField O))
        (TrivSqZeroExt.fstHom O (ResidueField O) (Fin d → ResidueField O)).toRingHom),
      (∀ x : F (DualNumber (ResidueField O)) (TrivSqZeroExt.fstHom O (ResidueField O) (ResidueField O)).toRingHom,
        ∃ (θ : TrivSqZeroExt (ResidueField O) (Fin d → ResidueField O) →ₐ[O] DualNumber (ResidueField O))
          (hθ : (TrivSqZeroExt.fstHom O (ResidueField O) (ResidueField O)).toRingHom.comp θ.toRingHom =
            (TrivSqZeroExt.fstHom O (ResidueField O) (Fin d → ResidueField O)).toRingHom),
          Frel (Fmap θ hθ ξ) x) ∧
      (∀ (θ θ' : TrivSqZeroExt (ResidueField O) (Fin d → ResidueField O) →ₐ[O] DualNumber (ResidueField O))
          (hθ : (TrivSqZeroExt.fstHom O (ResidueField O) (ResidueField O)).toRingHom.comp θ.toRingHom =
            (TrivSqZeroExt.fstHom O (ResidueField O) (Fin d → ResidueField O)).toRingHom)
          (hθ' : (TrivSqZeroExt.fstHom O (ResidueField O) (ResidueField O)).toRingHom.comp θ'.toRingHom =
            (TrivSqZeroExt.fstHom O (ResidueField O) (Fin d → ResidueField O)).toRingHom),
        Frel (Fmap θ hθ ξ) (Fmap θ' hθ' ξ) → θ = θ') := by sorry
