-- Prove2me | Theorems.Thm_Module_faithfullyFlat_pi_localizationAway_of_span_eq_top
-- name    : Module.faithfullyFlat_pi_localizationAway_of_span_eq_top
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:55.610395+00:00
-- url     : https://prove2.me/theorems/4fa2abc9-65cc-5115-a5ec-7127c078a9a7
-- title:
--   Finite principal Zariski covers are faithfully flat
-- statement:
--   Let $S$ be a commutative ring, let $k$ be a natural number and let $r : \mathrm{Fin}\,k \to S$ be a finite family of elements of $S$ whose set-theoretic range generates the unit ideal, i.e. $\mathrm{span}_S\{r_0,\dots,r_{k-1}\} = \top$. The conclusion is that the product ring $\prod_{i \in \mathrm{Fin}\,k} S[1/r_i]$, where $S[1/r_i]$ denotes the localisation of $S$ away from $r_i$ (i.e. at the multiplicative set of powers of $r_i$), is a faithfully flat $S$-module: it is flat over $S$, and tensoring with it kills no nonzero $S$-module. Note that the assertion is about the $S$-module structure on the finite product (equivalently, the $S$-algebra $\prod_i S[1/r_i]$) and that $k$ is allowed to be arbitrary; the hypothesis $\mathrm{span}(\mathrm{range}\,r) = \top$ forces $k \ge 1$ unless $S$ is the zero ring.
--
--   This is the standard statement that a finite cover of $\operatorname{Spec} S$ by principal open subsets $D(r_i)$ with $\bigcup_i D(r_i) = \operatorname{Spec} S$ gives a faithfully flat ring map $S \to \prod_i S[1/r_i]$. It serves the Zariski-descent steps for polarised abelian schemes, being cited in the construction of isomorphisms of such schemes from compatible local data over a principal open cover.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Module_faithfullyFlat_pi_localizationAway_of_span_eq_top.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

theorem Module.faithfullyFlat_pi_localizationAway_of_span_eq_top
    {S : Type u} [CommRing S] {k : ℕ} (r : Fin k → S) (hr : Ideal.span (Set.range r) = ⊤) :
    Module.FaithfullyFlat S (∀ i : Fin k, Localization.Away (r i)) := by sorry
