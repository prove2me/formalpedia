-- Prove2me | Theorems.Thm_Module_Grassmannian_exists_scheme_represents_and_isAffineOpen_chart_cover
-- name    : Module.Grassmannian.exists_scheme_represents_and_isAffineOpen_chart_cover
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:55.610395+00:00
-- url     : https://prove2.me/theorems/5c1eb028-559f-524f-9d50-7f44638a5219
-- title:
--   Representability of the Grassmannian functor by affine charts
-- statement:
--   Let $R$ be a commutative ring, $M$ an $R$-module and $k$ a natural number. The assertion is the existence of a scheme $\mathrm{Gr}$ (in the zeroth universe), a morphism $p : \mathrm{Gr} \to \operatorname{Spec} R$, for every commutative $R$-algebra $A$ a bijection $\mathrm{pt}_A$ from `Module.Grassmannian A (A ⊗[R] M) k` — the $A$-submodules $N \subseteq A \otimes_R M$ classified by Mathlib's Grassmannian type — onto the set of morphisms $g : \operatorname{Spec} A \to \mathrm{Gr}$ with $g$ followed by $p$ equal to $\operatorname{Spec}$ of the structure map $R \to A$, and an open subscheme $V_x \subseteq \mathrm{Gr}$ for each $k$-tuple $x : \mathrm{Fin}\,k \to M$, subject to four conditions: (i) naturality, namely for every $R$-algebra map $\varphi : A \to B$ and every $N$ over $A$, the morphism $\mathrm{pt}_B(\mathrm{map}\,\varphi\,N)$ equals $\operatorname{Spec}\varphi$ followed by $\mathrm{pt}_A(N)$; (ii) the supremum of the $V_x$ is the whole of $\mathrm{Gr}$; (iii) each $V_x$ is an affine open; (iv) for each $x$, each $A$ and each $N$, the set-theoretic image of $\mathrm{pt}_A(N)$ is contained in $V_x$ if and only if the $A$-linear map $A^k \to (A \otimes_R M)/N$ sending $v$ to $\sum_i v_i \cdot \overline{1 \otimes x_i}$ is bijective.
--
--   This is the representability half of Grothendieck's theorem on Grassmannians (EGA I, 9.7), here for an arbitrary $R$-module $M$ with no finiteness hypothesis, together with the standard affine chart cover indexed by $k$-tuples of elements of $M$. It is the input to the construction of the Plücker closed immersion of the Grassmannian into projective space.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Module_Grassmannian_exists_scheme_represents_and_isAffineOpen_chart_cover.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped TensorProduct
open CategoryTheory AlgebraicGeometry

theorem Module.Grassmannian.exists_scheme_represents_and_isAffineOpen_chart_cover
    (R : Type) [CommRing R] (M : Type) [AddCommGroup M] [Module R M] (k : ℕ) :
    ∃ (Gr : Scheme.{0}) (p : Gr ⟶ Spec (CommRingCat.of R))
      (pt : ∀ (A : Type) [CommRing A] [Algebra R A],
        Module.Grassmannian A (A ⊗[R] M) k ≃
          {g : Spec (CommRingCat.of A) ⟶ Gr // g ≫ p = Spec.map (CommRingCat.ofHom (algebraMap R A))})
      (V : (Fin k → M) → Gr.Opens),
      (∀ (A B : Type) [CommRing A] [CommRing B] [Algebra R A] [Algebra R B] (φ : A →ₐ[R] B)
          (N : Module.Grassmannian A (A ⊗[R] M) k),
        (pt B (Module.Grassmannian.map φ N)).1 = Spec.map (CommRingCat.ofHom φ.toRingHom) ≫ (pt A N).1) ∧
      (⨆ x, V x = ⊤) ∧ (∀ x, IsAffineOpen (V x)) ∧
      (∀ (x : Fin k → M) (A : Type) [CommRing A] [Algebra R A] (N : Module.Grassmannian A (A ⊗[R] M) k),
          Set.range (pt A N).1.base ⊆ (V x : Set Gr) ↔
            Function.Bijective fun v : Fin k → A =>
              ∑ i, v i • N.toSubmodule.mkQ ((1 : A) ⊗ₜ[R] x i)) := by sorry
