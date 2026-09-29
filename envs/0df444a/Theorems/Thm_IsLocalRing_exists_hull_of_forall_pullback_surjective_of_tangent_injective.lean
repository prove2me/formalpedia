-- Prove2me | Theorems.Thm_IsLocalRing_exists_hull_of_forall_pullback_surjective_of_tangent_injective
-- name    : IsLocalRing.exists_hull_of_forall_pullback_surjective_of_tangent_injective
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:57.878306+00:00
-- url     : https://prove2.me/theorems/c11e8935-9f45-5df1-a21e-cfe6079ec9b7
-- title:
--   Existence of a hull for a setoid-valued functor on Artinian algebras
-- statement:
--   Throughout, $O$ is a commutative Noetherian local ring which is complete for the adic topology of its maximal ideal, and $k = \mathrm{ResidueField}\,O$ with residue map $\mathrm{residue}\,O \colon O \to k$; all types range over a fixed universe.
--
--   The data are: a family $F$ assigning a type $F\,A\,\mathrm{res}_A$ to every commutative $O$-algebra $A$ together with a ring homomorphism $\mathrm{res}_A \colon A \to k$, and a relation $\mathrm{Frel}$ on each $F\,A\,\mathrm{res}_A$.
--
--   Hypothesis group *setoid* (`hrefl`, `hsymm`, `htrans`): $\mathrm{Frel}$ is reflexive, symmetric and transitive on each $F\,A\,\mathrm{res}_A$, so each $F\,A\,\mathrm{res}_A$ is partitioned into classes.
--
--   Hypothesis group *functoriality* (`Fmap`, `Fmap_rel`, `Fmap_id`, `Fmap_comp`): for every $O$-algebra homomorphism $f \colon A \to A'$ with $\mathrm{res}_{A'} \circ f = \mathrm{res}_A$ there is a map $\mathrm{Fmap}\,f \colon F\,A\,\mathrm{res}_A \to F\,A'\,\mathrm{res}_{A'}$; these maps carry $\mathrm{Frel}$-related elements to $\mathrm{Frel}$-related elements, $\mathrm{Fmap}$ of the identity of $A$ sends $x$ to an element $\mathrm{Frel}$-related to $x$, and for $f \colon A \to A'$, $g \colon A' \to A''$ compatible with the residue maps, $\mathrm{Fmap}\,(g \circ f)\,x$ is $\mathrm{Frel}$-related to $\mathrm{Fmap}\,g\,(\mathrm{Fmap}\,f\,x)$.
--
--   Hypothesis group *one class over $k$* (`x₀`, `hx₀`): an element $x_0 \in F\,k\,\mathrm{id}_k$ is given such that every element of $F\,k\,\mathrm{id}_k$ is $\mathrm{Frel}$-related to $x_0$.
--
--   Hypothesis group *gluing* (`hglue`): let $B, A', A'', A$ be Artinian local $O$-algebras equipped with surjective ring homomorphisms $\mathrm{res}_B, \mathrm{res}_{A'}, \mathrm{res}_{A''}, \mathrm{res}_A$ to $k$ whose composites with the structure maps from $O$ are $\mathrm{residue}\,O$, and let $p' \colon B \to A'$, $p'' \colon B \to A''$, $q' \colon A' \to A$, $q'' \colon A'' \to A$ be $O$-algebra homomorphisms compatible with these residue maps, such that $q' \circ p' = q'' \circ p''$, such that for all $a' \in A'$, $a'' \in A''$ with $q'(a') = q''(a'')$ there is a unique $b \in B$ with $p'(b) = a'$ and $p''(b) = a''$ (so $B$ is elementwise the fibre product of $A'$ and $A''$ over $A$), and such that $q''$ is surjective. Then for all $x' \in F\,A'\,\mathrm{res}_{A'}$ and $x'' \in F\,A''\,\mathrm{res}_{A''}$ with $\mathrm{Fmap}\,q'\,x'$ and $\mathrm{Fmap}\,q''\,x''$ $\mathrm{Frel}$-related, there exists $y \in F\,B\,\mathrm{res}_B$ with $\mathrm{Fmap}\,p'\,y$ related to $x'$ and $\mathrm{Fmap}\,p''\,y$ related to $x''$.
--
--   Hypothesis group *finite tangent space* (`r`, `e`, `he_rel`, `he_inj`, `he_smul`, `he_add`): writing $k[\varepsilon] = \mathrm{DualNumber}\,k$ with residue map the underlying ring homomorphism of $\mathrm{TrivSqZeroExt.fstHom}\,O\,k\,k$, there are a natural number $r$ and a map $e \colon F\,k[\varepsilon] \to (\mathrm{Fin}\,r \to k)$ such that: $\mathrm{Frel}$-related elements have equal image and conversely equal images force $\mathrm{Frel}$ (so $e$ induces an injection of the set of classes into $k^r$); for every $c \in k$ and every $O$-algebra endomorphism $\mu$ of $k[\varepsilon]$ compatible with $\mathrm{fstHom}$ and satisfying $\mathrm{snd}(\mu\,t) = c \cdot \mathrm{snd}\,t$ for all $t$, one has $e(\mathrm{Fmap}\,\mu\,x) = c \cdot e(x)$; and for every Artinian local $O$-algebra $B$ with surjective residue map $\mathrm{res}_B \colon B \to k$ compatible with $\mathrm{residue}\,O$ and all $O$-algebra homomorphisms $p_1, p_2, \sigma \colon B \to k[\varepsilon]$ compatible with $\mathrm{res}_B$ such that $(p_1, p_2)$ is jointly injective on $B$, such that any pair $t_1, t_2 \in k[\varepsilon]$ with $\mathrm{fst}\,t_1 = \mathrm{fst}\,t_2$ is of the form $(p_1 b, p_2 b)$, and such that $\mathrm{snd}(\sigma b) = \mathrm{snd}(p_1 b) + \mathrm{snd}(p_2 b)$ for all $b$, one has $e(\mathrm{Fmap}\,\sigma\,y) = e(\mathrm{Fmap}\,p_1\,y) + e(\mathrm{Fmap}\,p_2\,y)$ for all $y \in F\,B\,\mathrm{res}_B$.
--
--   The conclusion asserts the existence of a type $R$ carrying a commutative ring structure, a local ring structure, a Noetherian ring structure, an $O$-algebra structure and completeness for the adic topology of $\mathrm{maximalIdeal}\,R$, of a ring homomorphism $\mathrm{res}_R \colon R \to k$ with $\mathrm{res}_R \circ (\text{structure map } O \to R) = \mathrm{residue}\,O$, and of an assignment $\Xi$ which, given a commutative $O$-algebra $A$, proofs that $A$ is local and Artinian, a ring homomorphism $\mathrm{res}_A \colon A \to k$ that is surjective and satisfies $\mathrm{res}_A \circ (O \to A) = \mathrm{residue}\,O$, and an $O$-algebra homomorphism $u \colon R \to A$ with $\mathrm{res}_A \circ u = \mathrm{res}_R$, produces an element of $F\,A\,\mathrm{res}_A$. These are required to satisfy four conditions.
--
--   First, naturality: for Artinian local $O$-algebras $A$ and $A'$ with surjective residue maps to $k$ compatible with $\mathrm{residue}\,O$, every $O$-algebra homomorphism $f \colon A \to A'$ with $\mathrm{res}_{A'} \circ f = \mathrm{res}_A$, every $u \colon R \to A$ with $\mathrm{res}_A \circ u = \mathrm{res}_R$ and the attendant compatibility $\mathrm{res}_{A'} \circ (f \circ u) = \mathrm{res}_R$, the element $\Xi(f \circ u)$ is $\mathrm{Frel}$-related to $\mathrm{Fmap}\,f\,(\Xi(u))$.
--
--   Second, injectivity on the tangent space: given proofs that $k[\varepsilon]$ is local and Artinian, that $\mathrm{fstHom}$ is surjective and that it is compatible with $\mathrm{residue}\,O$, and given $O$-algebra homomorphisms $\theta, \theta' \colon R \to k[\varepsilon]$ with $\mathrm{fstHom} \circ \theta = \mathrm{res}_R = \mathrm{fstHom} \circ \theta'$, if $\Xi(\theta)$ and $\Xi(\theta')$ are $\mathrm{Frel}$-related then $\theta = \theta'$.
--
--   Third, surjectivity on the tangent space: with the same four proofs about $k[\varepsilon]$ as arguments, for every $x \in F\,k[\varepsilon]$ there exist $\theta \colon R \to k[\varepsilon]$ and a proof that $\mathrm{fstHom} \circ \theta = \mathrm{res}_R$ such that $\Xi(\theta)$ is $\mathrm{Frel}$-related to $x$.
--
--   Fourth, lifting along small principal surjections: for Artinian local $O$-algebras $A'$ and $A$ with surjective residue maps to $k$ compatible with $\mathrm{residue}\,O$, every surjective $O$-algebra homomorphism $q \colon A' \to A$ with $\mathrm{res}_A \circ q = \mathrm{res}_{A'}$, and every $t \in A'$ with $t \neq 0$, $t \in \ker \mathrm{res}_{A'}$, $m t = 0$ for all $m \in \ker \mathrm{res}_{A'}$ and $\{a \in A' : q(a) = 0\} = (t)$, the following holds: for every $u \colon R \to A$ with $\mathrm{res}_A \circ u = \mathrm{res}_R$ and every $\eta' \in F\,A'\,\mathrm{res}_{A'}$ such that $\mathrm{Fmap}\,q\,\eta'$ is $\mathrm{Frel}$-related to $\Xi(u)$, there exists an $O$-algebra homomorphism $u' \colon R \to A'$ with $q \circ u' = u$. Note that this last clause asserts only the existence of a lift of the point $u$; it asserts nothing relating $u'$ to $\eta'$, and the lifting property is demanded only for surjections whose kernel is principal and annihilated by the maximal ideal.
--
--   This is the existence half of Schlessinger's criterion: the pair $(R, \Xi)$ is a hull of the functor $F$, namely a morphism $h_R \to F$ which is bijective on $k[\varepsilon]$-points and smooth along small principal surjections. It feeds the representability statement [`IsLocalRing.exists_forall_algHom_bijective_of_forall_pullback_bijective_of_tangent_injective`](thm.html#IsLocalRing.exists_forall_algHom_bijective_of_forall_pullback_bijective_of_tangent_injective), from which universal deformation rings for Galois deformation problems are obtained.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_IsLocalRing_exists_hull_of_forall_pullback_surjective_of_tangent_injective.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open IsLocalRing in

theorem IsLocalRing.exists_hull_of_forall_pullback_surjective_of_tangent_injective
    (O : Type u) [CommRing O] [IsLocalRing O] [IsNoetherianRing O]
    [IsAdicComplete (maximalIdeal O) O]
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
    ∃ (R : Type u) (_ : CommRing R) (_ : IsLocalRing R) (_ : IsNoetherianRing R) (_ : Algebra O R)
      (_ : IsAdicComplete (maximalIdeal R) R)
      (resR : R →+* ResidueField O) (_ : resR.comp (algebraMap O R) = residue O)
      (Ξ : ∀ (A : Type u) [CommRing A] [Algebra O A], IsLocalRing A → IsArtinianRing A →
      ∀ (resA : A →+* ResidueField O), Function.Surjective resA →
        resA.comp (algebraMap O A) = residue O →
      ∀ (u : R →ₐ[O] A), resA.comp u.toRingHom = resR → F A resA),

      (∀ (A : Type u) [CommRing A] [Algebra O A] (hlA : IsLocalRing A) (haA : IsArtinianRing A)
        (resA : A →+* ResidueField O) (hsA : Function.Surjective resA)
        (hcA : resA.comp (algebraMap O A) = residue O)
        (A' : Type u) [CommRing A'] [Algebra O A'] (hlA' : IsLocalRing A') (haA' : IsArtinianRing A')
        (resA' : A' →+* ResidueField O) (hsA' : Function.Surjective resA')
        (hcA' : resA'.comp (algebraMap O A') = residue O)
        (f : A →ₐ[O] A') (hf : resA'.comp f.toRingHom = resA)
        (u : R →ₐ[O] A) (hu : resA.comp u.toRingHom = resR)
        (hfu : resA'.comp (f.comp u).toRingHom = resR),
        Frel (Ξ A' hlA' haA' resA' hsA' hcA' (f.comp u) hfu) (Fmap f hf (Ξ A hlA haA resA hsA hcA u hu))) ∧

      (∀ (hl : IsLocalRing (DualNumber (ResidueField O)))
        (ha : IsArtinianRing (DualNumber (ResidueField O)))
        (hs : Function.Surjective (TrivSqZeroExt.fstHom O (ResidueField O) (ResidueField O)).toRingHom)
        (hc : (TrivSqZeroExt.fstHom O (ResidueField O) (ResidueField O)).toRingHom.comp
          (algebraMap O (DualNumber (ResidueField O))) = residue O)
        (θ θ' : R →ₐ[O] DualNumber (ResidueField O))
        (hθ : (TrivSqZeroExt.fstHom O (ResidueField O) (ResidueField O)).toRingHom.comp θ.toRingHom = resR)
        (hθ' : (TrivSqZeroExt.fstHom O (ResidueField O) (ResidueField O)).toRingHom.comp θ'.toRingHom =
          resR),
        Frel (Ξ _ hl ha _ hs hc θ hθ) (Ξ _ hl ha _ hs hc θ' hθ') → θ = θ') ∧

      (∀ (hl : IsLocalRing (DualNumber (ResidueField O)))
        (ha : IsArtinianRing (DualNumber (ResidueField O)))
        (hs : Function.Surjective (TrivSqZeroExt.fstHom O (ResidueField O) (ResidueField O)).toRingHom)
        (hc : (TrivSqZeroExt.fstHom O (ResidueField O) (ResidueField O)).toRingHom.comp
          (algebraMap O (DualNumber (ResidueField O))) = residue O)
        (x : F (DualNumber (ResidueField O))
          (TrivSqZeroExt.fstHom O (ResidueField O) (ResidueField O)).toRingHom),
        ∃ (θ : R →ₐ[O] DualNumber (ResidueField O))
          (hθ : (TrivSqZeroExt.fstHom O (ResidueField O) (ResidueField O)).toRingHom.comp θ.toRingHom =
            resR), Frel (Ξ _ hl ha _ hs hc θ hθ) x) ∧

      (∀ (A' : Type u) [CommRing A'] [Algebra O A'] (hlA' : IsLocalRing A') (haA' : IsArtinianRing A')
        (resA' : A' →+* ResidueField O) (hsA' : Function.Surjective resA')
        (hcA' : resA'.comp (algebraMap O A') = residue O)
        (A : Type u) [CommRing A] [Algebra O A] (hlA : IsLocalRing A) (haA : IsArtinianRing A)
        (resA : A →+* ResidueField O) (hsA : Function.Surjective resA)
        (hcA : resA.comp (algebraMap O A) = residue O)
        (q : A' →ₐ[O] A) (hq : resA.comp q.toRingHom = resA'), Function.Surjective q →
        ∀ (t : A'), t ≠ 0 → t ∈ RingHom.ker resA' → (∀ m ∈ RingHom.ker resA', m * t = 0) →
        (∀ a : A', q a = 0 ↔ a ∈ Ideal.span {t}) →
        ∀ (u : R →ₐ[O] A) (hu : resA.comp u.toRingHom = resR) (η' : F A' resA'),
        Frel (Fmap q hq η') (Ξ A hlA haA resA hsA hcA u hu) → ∃ u' : R →ₐ[O] A', q.comp u' = u) := by sorry
