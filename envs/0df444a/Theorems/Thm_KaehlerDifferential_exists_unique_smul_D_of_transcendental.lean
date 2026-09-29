-- Prove2me | Theorems.Thm_KaehlerDifferential_exists_unique_smul_D_of_transcendental
-- name    : KaehlerDifferential.exists_unique_smul_D_of_transcendental
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:00.858323+00:00
-- url     : https://prove2.me/theorems/a237556d-2bdb-530a-8843-e382745f6740
-- title:
--   Unique coordinate of a differential along D x
-- statement:
--   Let $K$ be a field, $F$ a field equipped with a $K$-algebra structure, and $x \in F$ an element transcendental over $K$, i.e. not a root of any nonzero polynomial over $K$; assume moreover that $F$ is separable as an algebra over the intermediate field $K(x)$ obtained by adjoining the singleton $\{x\}$ to $K$ inside $F$. Then for every element $\omega$ of the module of Kähler differentials $\Omega_{F/K}$ there is a unique scalar $c \in F$ with $\omega = c \cdot D_{K,F}(x)$, where $D_{K,F} : F \to \Omega_{F/K}$ is the universal derivation and the product is the $F$-module action on $\Omega_{F/K}$. In other words, under these hypotheses $\Omega_{F/K}$ is free of rank one over $F$ with basis the single element $D_{K,F}(x)$, the uniqueness clause being stated in Lean's `∃!` form for the coordinate $c$.
--
--   This is the standard fact that for a separably generated extension $F/K(x)$ with $x$ transcendental the module of Kähler differentials of $F$ over $K$ is one-dimensional over $F$, spanned by $dx$; the scalar $c$ is the coordinate of $\omega$ with respect to $dx$. It provides the coordinate calculus for differentials on a curve, and is used in the analysis of orders and ramification of differentials at places, for instance in computing the order of $D$ of a uniformiser and the behaviour of differentials under pullback.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_KaehlerDifferential_exists_unique_smul_D_of_transcendental.lean

import Mathlib.RingTheory.Kaehler.Basic
import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
import Mathlib.FieldTheory.Separable
import Mathlib.RingTheory.Algebraic.Defs

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem KaehlerDifferential.exists_unique_smul_D_of_transcendental (K : Type*) [Field K] {F : Type*} [Field F] [Algebra K F] (x : F) (hx : Transcendental K x) [Algebra.IsSeparable (IntermediateField.adjoin K ({x} : Set F)) F] (ω : KaehlerDifferential K F) : ∃! c : F, ω = c • KaehlerDifferential.D K F x := by sorry
