-- Prove2me | Theorems.Thm_IsLocalRing_exists_forall_algHom_bijective_of_forall_pullback_bijective_of_tangent_injective
-- name    : IsLocalRing.exists_forall_algHom_bijective_of_forall_pullback_bijective_of_tangent_injective
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:57.878306+00:00
-- url     : https://prove2.me/theorems/5a1c9361-5e14-5211-9156-6fae6b345c03
-- title:
--   Pro-representability of a functor with bijective gluing
-- statement:
--   Throughout, $O$ is a Noetherian local ring, complete for the adic topology of its maximal ideal, and $k = \mathrm{ResidueField}\,O$ denotes its residue field; $\mathrm{residue}\,O \colon O \to k$ is the residue map. The data are taken in a single universe $u$.
--
--   **The functor.** `F` assigns to every commutative ring $A$ equipped with an $O$-algebra structure and a ring homomorphism $\mathrm{res}_A \colon A \to k$ a type $F(A,\mathrm{res}_A)$; `Frel` is a binary relation on each such type, assumed reflexive (`hrefl`), symmetric (`hsymm`) and transitive (`htrans`); and `Fmap` assigns to every $O$-algebra homomorphism $f \colon A \to A'$ with $\mathrm{res}_{A'} \circ f = \mathrm{res}_A$ a map $F(A,\mathrm{res}_A) \to F(A',\mathrm{res}_{A'})$. The functoriality hypotheses are `Fmap_rel` (each `Fmap f` carries `Frel`-related elements to `Frel`-related elements), `Fmap_id` (`Fmap` of the identity of $A$ is `Frel`-related to the identity map) and `Fmap_comp` (`Fmap` of a composite $g \circ f$ is pointwise `Frel`-related to `Fmap g` applied after `Fmap f`). Thus $F$ is a functor into sets-with-an-equivalence-relation, defined on all $O$-algebras over $k$, only the Artinian local ones mattering below.
--
--   **One class over the residue field (`x₀`, `hx₀`).** There is an element $x_0 \in F(k,\mathrm{id}_k)$ to which every element of $F(k,\mathrm{id}_k)$ is `Frel`-related.
--
--   **Gluing (`hglue`).** Let $B, A', A'', A$ be Artinian local $O$-algebras, each with a surjective ring homomorphism to $k$ ($\mathrm{res}_B, \mathrm{res}_{A'}, \mathrm{res}_{A''}, \mathrm{res}_A$) whose composite with the structure map from $O$ is $\mathrm{residue}\,O$, and let $p' \colon B \to A'$, $p'' \colon B \to A''$, $q' \colon A' \to A$, $q'' \colon A'' \to A$ be $O$-algebra homomorphisms compatible with these maps to $k$, such that $q' \circ p' = q'' \circ p''$, such that for all $a' \in A'$, $a'' \in A''$ with $q'(a') = q''(a'')$ there is a unique $b \in B$ with $p'(b) = a'$ and $p''(b) = a''$ (that is, $B$ is the fibre product $A' \times_A A''$ through $p', p''$), and such that $q''$ is surjective. Then: (i) for all $x' \in F(A',\mathrm{res}_{A'})$ and $x'' \in F(A'',\mathrm{res}_{A''})$ whose images under `Fmap q'` and `Fmap q''` are `Frel`-related, there is $y \in F(B,\mathrm{res}_B)$ with `Fmap p'` $y$ related to $x'$ and `Fmap p''` $y$ related to $x''$; and (ii) any $y_1, y_2 \in F(B,\mathrm{res}_B)$ whose images under `Fmap p'` are related and whose images under `Fmap p''` are related are themselves `Frel`-related. So $F(B) \to F(A') \times_{F(A)} F(A'')$ is bijective on classes.
--
--   **Tangent hypotheses.** There are a natural number $r$ and a map
--   $$e \colon F\bigl(k[\varepsilon],\ \mathrm{fst}\bigr) \longrightarrow (\mathrm{Fin}\ r \to k),$$
--   where $k[\varepsilon] = \mathrm{DualNumber}\,k$ is the dual number algebra and the map to $k$ is the first-coordinate homomorphism `TrivSqZeroExt.fstHom O k k`. Four hypotheses are imposed on $e$: `he_rel`, that $e$ is constant on `Frel`-classes; `he_inj`, that conversely $e\,x = e\,y$ implies `Frel x y`; `he_smul`, that for $c \in k$ and an $O$-algebra endomorphism $\mu$ of $k[\varepsilon]$ compatible with the first-coordinate map and satisfying $\mathrm{snd}(\mu t) = c \cdot \mathrm{snd}(t)$ for all $t$, one has $e(\mathrm{Fmap}\ \mu\ x) = c \cdot e(x)$; and `he_add`, that for an Artinian local $O$-algebra $B$ with surjective $\mathrm{res}_B$ compatible with $\mathrm{residue}\,O$ and three $O$-algebra homomorphisms $p_1, p_2, \sigma \colon B \to k[\varepsilon]$ compatible with $\mathrm{res}_B$ through the first-coordinate map, such that $p_1$ and $p_2$ jointly separate the elements of $B$, such that every pair $t_1, t_2 \in k[\varepsilon]$ with $\mathrm{fst}(t_1) = \mathrm{fst}(t_2)$ is of the form $(p_1 b, p_2 b)$, and such that $\mathrm{snd}(\sigma b) = \mathrm{snd}(p_1 b) + \mathrm{snd}(p_2 b)$ for all $b \in B$, one has $e(\mathrm{Fmap}\ \sigma\ y) = e(\mathrm{Fmap}\ p_1\ y) + e(\mathrm{Fmap}\ p_2\ y)$ for every $y \in F(B,\mathrm{res}_B)$. Together these say that $e$ identifies the `Frel`-classes on the tangent set $F(k[\varepsilon])$ injectively with a subset of $k^r$, compatibly with the $k$-scaling and the addition coming from the dual numbers.
--
--   **Conclusion.** Under these hypotheses there exist a type $R$, a commutative ring structure on $R$ making it a local Noetherian $O$-algebra which is complete for the adic topology of its maximal ideal, a ring homomorphism $\mathrm{res}_R \colon R \to k$ with $\mathrm{res}_R \circ (\text{structure map } O \to R) = \mathrm{residue}\,O$, and a map $\beta$ which, for every Artinian local $O$-algebra $A$ with a surjective $\mathrm{res}_A \colon A \to k$ satisfying $\mathrm{res}_A \circ (O \to A) = \mathrm{residue}\,O$, sends each $x \in F(A,\mathrm{res}_A)$ to an $O$-algebra homomorphism $\beta_A(x) \colon R \to A$, such that all of the following hold:
--
--   1. for all such $A$, $\mathrm{res}_A$, and all $x$: $\mathrm{res}_A \circ \beta_A(x) = \mathrm{res}_R$;
--
--   2. for all such $A$ and all $x, y$: if `Frel x y` then $\beta_A(x) = \beta_A(y)$;
--
--   3. for all such $A$ and $A'$ and every $O$-algebra homomorphism $f \colon A \to A'$ with $\mathrm{res}_{A'} \circ f = \mathrm{res}_A$, and every $x \in F(A,\mathrm{res}_A)$: $\beta_{A'}(\mathrm{Fmap}\ f\ x) = f \circ \beta_A(x)$;
--
--   4. for all such $A$ and all $x, y$: if $\beta_A(x) = \beta_A(y)$ then `Frel x y`;
--
--   5. for all such $A$ and every $O$-algebra homomorphism $\chi \colon R \to A$ with $\mathrm{res}_A \circ \chi = \mathrm{res}_R$, there is $x \in F(A,\mathrm{res}_A)$ with $\beta_A(x) = \chi$.
--
--   That is, $\beta$ induces, naturally in $A$, a bijection between the set of `Frel`-classes in $F(A,\mathrm{res}_A)$ and the set of $O$-algebra homomorphisms $R \to A$ compatible with $\mathrm{res}_R$ and $\mathrm{res}_A$: the functor is pro-represented by $R$.
--
--   This is Schlessinger's criterion in its pro-representable form, stated for a functor valued in sets equipped with an equivalence relation (isomorphism classes of a functor in groupoids), with the gluing condition strengthened to bijectivity along all cartesian squares with one surjective leg, so that a genuine pro-representing object rather than merely a hull is produced. It is obtained by combining the construction of a hull from the same data with the passage from a hull to a pro-representation, and is applied to deformation functors of special formal $O_D$-modules in the Čerednik–Drinfeld setting.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_IsLocalRing_exists_forall_algHom_bijective_of_forall_pullback_bijective_of_tangent_injective.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open IsLocalRing in

theorem IsLocalRing.exists_forall_algHom_bijective_of_forall_pullback_bijective_of_tangent_injective
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
        (∀ (x' : F A' resA') (x'' : F A'' resA''), Frel (Fmap q' hq' x') (Fmap q'' hq'' x'') →
            ∃ y : F B resB, Frel (Fmap p' hp' y) x' ∧ Frel (Fmap p'' hp'' y) x'') ∧
        (∀ (y₁ y₂ : F B resB), Frel (Fmap p' hp' y₁) (Fmap p' hp' y₂) →
            Frel (Fmap p'' hp'' y₁) (Fmap p'' hp'' y₂) → Frel y₁ y₂))

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
