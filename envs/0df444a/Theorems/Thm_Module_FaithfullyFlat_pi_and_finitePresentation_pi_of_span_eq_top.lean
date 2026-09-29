-- Prove2me | Theorems.Thm_Module_FaithfullyFlat_pi_and_finitePresentation_pi_of_span_eq_top
-- name    : Module.FaithfullyFlat.pi_and_finitePresentation_pi_of_span_eq_top
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:55.610395+00:00
-- url     : https://prove2.me/theorems/b315aa5d-2742-5c5c-8b25-3a6adec62f94
-- title:
--   Finite product over a Zariski cover is faithfully flat, finitely presented
-- statement:
--   Let $S$ be a commutative ring and let $\iota$ be a finite type with decidable equality. Given a family $g : \iota \to S$ whose range generates the unit ideal, $\mathrm{span}(\{g_i\}) = \top$, and a family of commutative rings $C_i$, each carrying an $S$-algebra structure and an algebra structure over the away localisation $\mathrm{Localization.Away}(g_i) = S[1/g_i]$, compatibly in the sense that $S \to S[1/g_i] \to C_i$ is a scalar tower, assume that for every $i$ the module $C_i$ is faithfully flat over $S[1/g_i]$ and that $C_i$ is of finite presentation as an $S[1/g_i]$-algebra. The conclusion is the conjunction of two assertions: the product module $\prod_i C_i$ is faithfully flat over $S$, and the product ring $\prod_i C_i$ is of finite presentation as an $S$-algebra (for the $S$-algebra structure on the product coming from the componentwise structures).
--
--   This is the standard Zariski-descent assembly step: faithful flatness and finite presentation of a finite product of algebras defined over the members $D(g_i)$ of an affine open cover of $\operatorname{Spec} S$. It is used to build a single faithfully flat, finitely presented base extension out of locally given data, and is invoked in the construction of polarised abelian schemes from local pullback data and in the Čerednik–Drinfeld construction of fake elliptic curves, where local algebras at maximal ideals are glued into one cover algebra.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Module_FaithfullyFlat_pi_and_finitePresentation_pi_of_span_eq_top.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem Module.FaithfullyFlat.pi_and_finitePresentation_pi_of_span_eq_top
    {S : Type} [CommRing S] {ι : Type} [Fintype ι] [DecidableEq ι] (g : ι → S) (hg : Ideal.span (Set.range g) = ⊤)
    (C : ι → Type) [∀ i, CommRing (C i)] [∀ i, Algebra S (C i)] [∀ i, Algebra (Localization.Away (g i)) (C i)]
    [∀ i, IsScalarTower S (Localization.Away (g i)) (C i)]
    (hff : ∀ i, Module.FaithfullyFlat (Localization.Away (g i)) (C i))
    (hfp : ∀ i, Algebra.FinitePresentation (Localization.Away (g i)) (C i)) :
    Module.FaithfullyFlat S (∀ i, C i) ∧ Algebra.FinitePresentation S (∀ i, C i) := by sorry
