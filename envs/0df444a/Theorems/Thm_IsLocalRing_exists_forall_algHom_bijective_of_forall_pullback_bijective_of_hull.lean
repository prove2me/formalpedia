-- Prove2me | Theorems.Thm_IsLocalRing_exists_forall_algHom_bijective_of_forall_pullback_bijective_of_hull
-- name    : IsLocalRing.exists_forall_algHom_bijective_of_forall_pullback_bijective_of_hull
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:57.878306+00:00
-- url     : https://prove2.me/theorems/dc94010f-fc77-5c30-ad1d-789100e02366
-- title:
--   Universality of a hull under bijective gluing
-- statement:
--   Throughout, $O$ is a commutative local ring and $k =$ `ResidueField O` its residue field; all rings live in a fixed universe. The deformation-theoretic data consist of a family of types and a relation on it:
--
--   **The setoid-valued functor.** For every commutative $O$-algebra $A$ and every ring homomorphism $\mathrm{res}_A : A \to k$, a type $F\,A\,\mathrm{res}_A$ is given, together with a relation $Frel$ on each such type, and a transport operation $Fmap$ which, for an $O$-algebra homomorphism $f : A \to A'$ satisfying $\mathrm{res}_{A'} \circ f = \mathrm{res}_A$, maps $F\,A\,\mathrm{res}_A$ to $F\,A'\,\mathrm{res}_{A'}$. The hypotheses `hrefl`, `hsymm`, `htrans` say that $Frel$ is reflexive, symmetric and transitive on each $F\,A\,\mathrm{res}_A$; `Fmap_rel` says that each $Fmap\,f$ sends $Frel$-related elements to $Frel$-related elements; `Fmap_id` says that $Fmap$ of the identity algebra homomorphism sends $x$ to an element $Frel$-related to $x$; and `Fmap_comp` says that $Fmap$ of a composite $g \circ f$ sends $x$ to an element $Frel$-related to $Fmap\,g\,(Fmap\,f\,x)$. Thus functoriality is required only up to $Frel$, not on the nose.
--
--   **Triviality on the residue field (H0).** An element $x_0 \in F\,k\,(\mathrm{id}_k)$ is given (the residue map of $k$ being the identity), and `hx₀` requires every element of $F\,k\,(\mathrm{id}_k)$ to be $Frel$-related to $x_0$; so $F(k)$ is a single nonempty $Frel$-class.
--
--   **Bijective gluing (`hglue`).** Let $B$, $A'$, $A''$, $A$ be Artinian local $O$-algebras, each equipped with a ring homomorphism to $k$ which is surjective and whose composite with the structure map of $O$ is the residue map `residue O`. Let $p' : B \to A'$, $p'' : B \to A''$, $q' : A' \to A$, $q'' : A'' \to A$ be $O$-algebra homomorphisms compatible with these maps to $k$ in the evident sense ($\mathrm{res}_{A'} \circ p' = \mathrm{res}_B$, $\mathrm{res}_{A''} \circ p'' = \mathrm{res}_B$, $\mathrm{res}_A \circ q' = \mathrm{res}_{A'}$, $\mathrm{res}_A \circ q'' = \mathrm{res}_{A''}$). Assume $q' \circ p' = q'' \circ p''$, that the square is cartesian elementwise, i.e. for all $a' \in A'$ and $a'' \in A''$ with $q'(a') = q''(a'')$ there is a unique $b \in B$ with $p'(b) = a'$ and $p''(b) = a''$, and that $q''$ is surjective. Then two conclusions are required: first, for all $x' \in F\,A'\,\mathrm{res}_{A'}$ and $x'' \in F\,A''\,\mathrm{res}_{A''}$ with $Frel\,(Fmap\,q'\,x')\,(Fmap\,q''\,x'')$ there exists $y \in F\,B\,\mathrm{res}_B$ with $Frel\,(Fmap\,p'\,y)\,x'$ and $Frel\,(Fmap\,p''\,y)\,x''$; second, if $y_1, y_2 \in F\,B\,\mathrm{res}_B$ satisfy $Frel\,(Fmap\,p'\,y_1)\,(Fmap\,p'\,y_2)$ and $Frel\,(Fmap\,p''\,y_1)\,(Fmap\,p''\,y_2)$, then $Frel\,y_1\,y_2$. In other words, $F(B) \to F(A') \times_{F(A)} F(A'')$ is bijective on $Frel$-classes.
--
--   **The candidate hull.** $R$ is a commutative $O$-algebra with a ring homomorphism $\mathrm{res}_R : R \to k$ whose composite with the structure map of $O$ is `residue O` (hypothesis `hresR`); no completeness, noetherianness or local hypothesis is imposed on $R$. The datum $\Xi$ assigns, to every commutative $O$-algebra $A$ together with proofs that $A$ is local and Artinian, every ring homomorphism $\mathrm{res}_A : A \to k$ that is surjective and satisfies $\mathrm{res}_A \circ (\text{structure map of } O) = \mathrm{res}_A$'s required value `residue O`, and every $O$-algebra homomorphism $u : R \to A$ with $\mathrm{res}_A \circ u = \mathrm{res}_R$, an element $\Xi(u) \in F\,A\,\mathrm{res}_A$.
--
--   **Axioms on $\Xi$.** `Ξ_nat` (naturality up to $Frel$): for $A, A'$ Artinian local as above and $f : A \to A'$ compatible with the residue maps, and $u : R \to A$ compatible with $\mathrm{res}_R$, one has $Frel\,(\Xi(f \circ u))\,(Fmap\,f\,(\Xi(u)))$. `Ξ_inj` and `Ξ_surj` concern the dual numbers $k[\varepsilon] =$ `DualNumber (ResidueField O)` with residue map the first-coordinate projection `TrivSqZeroExt.fstHom O k k` (the required proofs that $k[\varepsilon]$ is local and Artinian and that this projection is surjective and compatible are taken as hypotheses): `Ξ_inj` requires that $Frel\,(\Xi(\theta))\,(\Xi(\theta'))$ implies $\theta = \theta'$ for compatible $\theta, \theta' : R \to k[\varepsilon]$, and `Ξ_surj` requires every $x \in F\,k[\varepsilon]$ to be $Frel$-related to $\Xi(\theta)$ for some compatible $\theta : R \to k[\varepsilon]$. `Ξ_lift` is the lifting (smoothness) property along small principal surjections: given Artinian local $A'$ and $A$ with surjective compatible residue maps, a surjective $O$-algebra homomorphism $q : A' \to A$ with $\mathrm{res}_A \circ q = \mathrm{res}_{A'}$, an element $t \in A'$ with $t \neq 0$, $t \in \ker \mathrm{res}_{A'}$ and $mt = 0$ for all $m \in \ker \mathrm{res}_{A'}$, such that $q(a) = 0$ if and only if $a$ lies in the ideal generated by $t$, and given $u : R \to A$ compatible with $\mathrm{res}_R$ and $\eta' \in F\,A'\,\mathrm{res}_{A'}$ with $Frel\,(Fmap\,q\,\eta')\,(\Xi(u))$, there exists $u' : R \to A'$ with $q \circ u' = u$.
--
--   **Conclusion.** Under these hypotheses there exists a family $\beta$ assigning, to every Artinian local $O$-algebra $A$ and every surjective ring homomorphism $\mathrm{res}_A : A \to k$ with $\mathrm{res}_A \circ (\text{structure map}) =$ `residue O`, a map $\beta_A : F\,A\,\mathrm{res}_A \to (R \to_{O\text{-alg}} A)$, such that for all such $A$ and $\mathrm{res}_A$:
--
--   1. $\mathrm{res}_A \circ \beta_A(x) = \mathrm{res}_R$ for every $x \in F\,A\,\mathrm{res}_A$;
--
--   2. $\beta_A$ is constant on $Frel$-classes: $Frel\,x\,y$ implies $\beta_A(x) = \beta_A(y)$;
--
--   3. $\beta$ is natural: for $A'$ a further Artinian local $O$-algebra with surjective compatible $\mathrm{res}_{A'}$ and $f : A \to A'$ an $O$-algebra homomorphism with $\mathrm{res}_{A'} \circ f = \mathrm{res}_A$, one has $\beta_{A'}(Fmap\,f\,x) = f \circ \beta_A(x)$;
--
--   4. $\beta_A$ is injective on $Frel$-classes: $\beta_A(x) = \beta_A(y)$ implies $Frel\,x\,y$;
--
--   5. $\beta_A$ is surjective onto compatible homomorphisms: for every $O$-algebra homomorphism $\chi : R \to A$ with $\mathrm{res}_A \circ \chi = \mathrm{res}_R$ there exists $x \in F\,A\,\mathrm{res}_A$ with $\beta_A(x) = \chi$.
--
--   The conclusion asserts nothing about $\Xi$ itself; $\Xi$ enters only through the hypotheses, and $\beta$ is the resulting identification of $F$ with the functor of points of $R$ on $Frel$-classes.
--
--   This is the second half of Schlessinger's Theorem 2.11: a hull of a functor satisfying the additional gluing condition (H4) is already universal, so that $F$ is identified with $\mathrm{Hom}_O(R, -)$ on $Frel$-classes over Artinian local $O$-algebras with residue field $k$. It is used by [`IsLocalRing.exists_forall_algHom_bijective_of_forall_pullback_bijective_of_tangent_injective`](thm.html#IsLocalRing.exists_forall_algHom_bijective_of_forall_pullback_bijective_of_tangent_injective), in the representability theory underlying the construction of universal deformation rings of Galois representations.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_IsLocalRing_exists_forall_algHom_bijective_of_forall_pullback_bijective_of_hull.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open IsLocalRing in

theorem IsLocalRing.exists_forall_algHom_bijective_of_forall_pullback_bijective_of_hull
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
        (∀ (x' : F A' resA') (x'' : F A'' resA''), Frel (Fmap q' hq' x') (Fmap q'' hq'' x'') →
            ∃ y : F B resB, Frel (Fmap p' hp' y) x' ∧ Frel (Fmap p'' hp'' y) x'') ∧
        (∀ (y₁ y₂ : F B resB), Frel (Fmap p' hp' y₁) (Fmap p' hp' y₂) →
            Frel (Fmap p'' hp'' y₁) (Fmap p'' hp'' y₂) → Frel y₁ y₂))

    (R : Type u) [CommRing R] [Algebra O R] (resR : R →+* ResidueField O)
    (hresR : resR.comp (algebraMap O R) = residue O)
    (Ξ : ∀ (A : Type u) [CommRing A] [Algebra O A], IsLocalRing A → IsArtinianRing A →
      ∀ (resA : A →+* ResidueField O), Function.Surjective resA →
        resA.comp (algebraMap O A) = residue O →
      ∀ (u : R →ₐ[O] A), resA.comp u.toRingHom = resR → F A resA)

    (Ξ_nat : ∀ (A : Type u) [CommRing A] [Algebra O A] (hlA : IsLocalRing A) (haA : IsArtinianRing A)
        (resA : A →+* ResidueField O) (hsA : Function.Surjective resA)
        (hcA : resA.comp (algebraMap O A) = residue O)
        (A' : Type u) [CommRing A'] [Algebra O A'] (hlA' : IsLocalRing A') (haA' : IsArtinianRing A')
        (resA' : A' →+* ResidueField O) (hsA' : Function.Surjective resA')
        (hcA' : resA'.comp (algebraMap O A') = residue O)
        (f : A →ₐ[O] A') (hf : resA'.comp f.toRingHom = resA)
        (u : R →ₐ[O] A) (hu : resA.comp u.toRingHom = resR)
        (hfu : resA'.comp (f.comp u).toRingHom = resR),
        Frel (Ξ A' hlA' haA' resA' hsA' hcA' (f.comp u) hfu) (Fmap f hf (Ξ A hlA haA resA hsA hcA u hu)))

    (Ξ_inj : ∀ (hl : IsLocalRing (DualNumber (ResidueField O)))
        (ha : IsArtinianRing (DualNumber (ResidueField O)))
        (hs : Function.Surjective (TrivSqZeroExt.fstHom O (ResidueField O) (ResidueField O)).toRingHom)
        (hc : (TrivSqZeroExt.fstHom O (ResidueField O) (ResidueField O)).toRingHom.comp
          (algebraMap O (DualNumber (ResidueField O))) = residue O)
        (θ θ' : R →ₐ[O] DualNumber (ResidueField O))
        (hθ : (TrivSqZeroExt.fstHom O (ResidueField O) (ResidueField O)).toRingHom.comp θ.toRingHom = resR)
        (hθ' : (TrivSqZeroExt.fstHom O (ResidueField O) (ResidueField O)).toRingHom.comp θ'.toRingHom =
          resR),
        Frel (Ξ _ hl ha _ hs hc θ hθ) (Ξ _ hl ha _ hs hc θ' hθ') → θ = θ')

    (Ξ_surj : ∀ (hl : IsLocalRing (DualNumber (ResidueField O)))
        (ha : IsArtinianRing (DualNumber (ResidueField O)))
        (hs : Function.Surjective (TrivSqZeroExt.fstHom O (ResidueField O) (ResidueField O)).toRingHom)
        (hc : (TrivSqZeroExt.fstHom O (ResidueField O) (ResidueField O)).toRingHom.comp
          (algebraMap O (DualNumber (ResidueField O))) = residue O)
        (x : F (DualNumber (ResidueField O))
          (TrivSqZeroExt.fstHom O (ResidueField O) (ResidueField O)).toRingHom),
        ∃ (θ : R →ₐ[O] DualNumber (ResidueField O))
          (hθ : (TrivSqZeroExt.fstHom O (ResidueField O) (ResidueField O)).toRingHom.comp θ.toRingHom =
            resR), Frel (Ξ _ hl ha _ hs hc θ hθ) x)

    (Ξ_lift : ∀ (A' : Type u) [CommRing A'] [Algebra O A'] (hlA' : IsLocalRing A') (haA' : IsArtinianRing A')
        (resA' : A' →+* ResidueField O) (hsA' : Function.Surjective resA')
        (hcA' : resA'.comp (algebraMap O A') = residue O)
        (A : Type u) [CommRing A] [Algebra O A] (hlA : IsLocalRing A) (haA : IsArtinianRing A)
        (resA : A →+* ResidueField O) (hsA : Function.Surjective resA)
        (hcA : resA.comp (algebraMap O A) = residue O)
        (q : A' →ₐ[O] A) (hq : resA.comp q.toRingHom = resA'), Function.Surjective q →
        ∀ (t : A'), t ≠ 0 → t ∈ RingHom.ker resA' → (∀ m ∈ RingHom.ker resA', m * t = 0) →
        (∀ a : A', q a = 0 ↔ a ∈ Ideal.span {t}) →
        ∀ (u : R →ₐ[O] A) (hu : resA.comp u.toRingHom = resR) (η' : F A' resA'),
        Frel (Fmap q hq η') (Ξ A hlA haA resA hsA hcA u hu) → ∃ u' : R →ₐ[O] A', q.comp u' = u) :
    ∃
      (β : ∀ (A : Type u) [CommRing A] [IsLocalRing A] [IsArtinianRing A] [Algebra O A]
        (resA : A →+* ResidueField O), Function.Surjective resA →
        resA.comp (algebraMap O A) = residue O → F A resA → (R →ₐ[O] A)),
      (∀ (A : Type u) [CommRing A] [IsLocalRing A] [IsArtinianRing A] [Algebra O A]
          (resA : A →+* ResidueField O) (hs : Function.Surjective resA)
          (hc : resA.comp (algebraMap O A) = residue O) (x : F A resA),
        resA.comp (β A resA hs hc x).toRingHom = resR) ∧
      (∀ (A : Type u) [CommRing A] [IsLocalRing A] [IsArtinianRing A] [Algebra O A]
          (resA : A →+* ResidueField O) (hs : Function.Surjective resA)
          (hc : resA.comp (algebraMap O A) = residue O) (x y : F A resA),
        Frel x y → β A resA hs hc x = β A resA hs hc y) ∧
      (∀ (A : Type u) [CommRing A] [IsLocalRing A] [IsArtinianRing A] [Algebra O A]
          (resA : A →+* ResidueField O) (hs : Function.Surjective resA)
          (hc : resA.comp (algebraMap O A) = residue O)
          (A' : Type u) [CommRing A'] [IsLocalRing A'] [IsArtinianRing A'] [Algebra O A']
          (resA' : A' →+* ResidueField O) (hs' : Function.Surjective resA')
          (hc' : resA'.comp (algebraMap O A') = residue O)
          (f : A →ₐ[O] A') (hf : resA'.comp f.toRingHom = resA) (x : F A resA),
        β A' resA' hs' hc' (Fmap f hf x) = f.comp (β A resA hs hc x)) ∧
      (∀ (A : Type u) [CommRing A] [IsLocalRing A] [IsArtinianRing A] [Algebra O A]
          (resA : A →+* ResidueField O) (hs : Function.Surjective resA)
          (hc : resA.comp (algebraMap O A) = residue O) (x y : F A resA),
        β A resA hs hc x = β A resA hs hc y → Frel x y) ∧
      (∀ (A : Type u) [CommRing A] [IsLocalRing A] [IsArtinianRing A] [Algebra O A]
          (resA : A →+* ResidueField O) (hs : Function.Surjective resA)
          (hc : resA.comp (algebraMap O A) = residue O) (χ : R →ₐ[O] A),
        resA.comp χ.toRingHom = resR → ∃ x : F A resA, β A resA hs hc x = χ) := by sorry
