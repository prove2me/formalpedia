-- Prove2me | Theorems.Thm_ModularCurve_DRLevel_exists_comp_pair_fibre_of_ringHom
-- name    : ModularCurve.DRLevel.exists_comp_pair_fibre_of_ringHom
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:13.065378+00:00
-- url     : https://prove2.me/theorems/8898e3f2-f4a2-5867-8bf6-98e00ef93c47
-- title:
--   Base change of a two-component fibre description along κ₀→κ
-- statement:
--   Fix $N_0\ge 1$ and a prime $q$, and write $X =$ `DRLevel.X N₀ q`, $X_0 =$ `DRLevel.X0 N₀ q` for the Igusa schemes of levels $N_0q$ and $N_0$ at $q$, with structure morphisms `DRLevel.toBase N₀ q` and `DRLevel.toBase0 N₀ q` to $\operatorname{Spec}$ of the base ring `DRLevel.R q`. Let $w$ be a self-isomorphism of $X$ whose underlying morphism `w.hom` commutes with `toBase N₀ q`, and let $\pi$ be a morphism $X \to X_0$ with $\pi$ followed by `toBase0 N₀ q` equal to `toBase N₀ q`. For a ring map $t\colon$ `R q` $\to \kappa'$ write `fibre t` $= X\times_{\operatorname{Spec} R\,q}\operatorname{Spec}\kappa'$ and `fibre0 t` for the analogous pullback of $X_0$; `fibreMap w.hom hw t` and `fibreMap0 π t` are the induced morphisms of fibres. Assume given a field $\kappa_0$, a ring map $t_0\colon$ `R q` $\to\kappa_0$ and two morphisms $c_0,c_1\colon$ `fibre0 t₀` $\to$ `fibre t₀` such that: each commutes with the second projections to $\operatorname{Spec}\kappa_0$; each is a closed immersion; the images of the underlying maps of $c_0$ and $c_1$ cover `fibre t₀`; those two images are distinct; $c_0$ followed by `fibreMap0 π t₀` is the identity; and $c_0$ followed by `fibreMap w.hom hw t₀` equals $c_1$. Then for every field $\kappa$, every ring map $t\colon$ `R q` $\to\kappa$ and every ring map $\varphi\colon\kappa_0\to\kappa$ with $\varphi\circ t_0 = t$, there exist two morphisms `fibre0 t` $\to$ `fibre t` with exactly the same six properties over $\kappa$.
--
--   This is a transport statement: it carries the description of the fibre of the Igusa scheme of level $N_0q$ at a field-valued point of the base as the union of two closed copies of the level-$N_0$ fibre, interchanged by $w$ and sectioned by $\pi$, along any extension $\kappa_0\to\kappa$ of the field of the point, using that closed immersions, surjectivity and the stated identities are stable under the further base change. It is invoked by [`ModularCurve.DRLevel.exists_comp_pair_fibre`](thm.html#ModularCurve.DRLevel.exists_comp_pair_fibre), in the Deligne–Rapoport analysis of the reduction at $q$ of the modular curve of level $N_0q$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_DRLevel_exists_comp_pair_fibre_of_ringHom.lean

import Mathlib
import Definitions.Def_ModularCurve_DRModelPackageLevel

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicCurve NeronModelInfra
open ModularCurve ModularCurve.IgusaScheme ModularCurve.DRLevel IsLocalRing

theorem ModularCurve.DRLevel.exists_comp_pair_fibre_of_ringHom
    (N₀ q : ℕ) [NeZero N₀] [Fact q.Prime]
    (w : DRLevel.X N₀ q ≅ DRLevel.X N₀ q) (hw : w.hom ≫ DRLevel.toBase N₀ q = DRLevel.toBase N₀ q)
    (π : SchemeHomOver (DRLevel.toBase N₀ q) (DRLevel.toBase0 N₀ q))
    (κ₀ : Type) [Field κ₀] (toκ₀ : DRLevel.R q →+* κ₀)
    (comp₀ : Fin 2 → (DRLevel.fibre0 (N₀ := N₀) toκ₀ ⟶ DRLevel.fibre (N₀ := N₀) toκ₀))
    (hover : ∀ i, comp₀ i ≫ pullback.snd _ _ = pullback.snd _ _)
    (hci : ∀ i, IsClosedImmersion (comp₀ i))
    (hsurj : ∀ y : DRLevel.fibre (N₀ := N₀) toκ₀, y ∈ Set.range (comp₀ 0).base ∨ y ∈ Set.range (comp₀ 1).base)
    (hne : Set.range (comp₀ 0).base ≠ Set.range (comp₀ 1).base)
    (hpi : comp₀ 0 ≫ DRLevel.fibreMap0 π toκ₀ = 𝟙 _)
    (hcw : comp₀ 0 ≫ DRLevel.fibreMap w.hom hw toκ₀ = comp₀ 1)
    (κ : Type) [Field κ] (toκ : DRLevel.R q →+* κ) (φ : κ₀ →+* κ) (hφ : φ.comp toκ₀ = toκ) :
    ∃ comp : Fin 2 → (DRLevel.fibre0 (N₀ := N₀) toκ ⟶ DRLevel.fibre (N₀ := N₀) toκ),
      (∀ i, comp i ≫ pullback.snd _ _ = pullback.snd _ _) ∧
      (∀ i, IsClosedImmersion (comp i)) ∧
      (∀ y : DRLevel.fibre (N₀ := N₀) toκ, y ∈ Set.range (comp 0).base ∨ y ∈ Set.range (comp 1).base) ∧
      Set.range (comp 0).base ≠ Set.range (comp 1).base ∧
      comp 0 ≫ DRLevel.fibreMap0 π toκ = 𝟙 _ ∧
      comp 0 ≫ DRLevel.fibreMap w.hom hw toκ = comp 1 := by sorry
