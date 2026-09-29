-- Prove2me | Theorems.Thm_InnerProductSpace_exists_mem_norm_sub_lt_of_exists_mem_span_orbit_of_average
-- name    : InnerProductSpace.exists_mem_norm_sub_lt_of_exists_mem_span_orbit_of_average
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:57.515241+00:00
-- url     : https://prove2.me/theorems/d25afd25-4225-5ab2-8ecb-48a1e2536cc1
-- title:
--   Averaging recovers a vector of a cyclic span
-- statement:
--   Let $G$ be a group, $L$ a complex vector space, and $H$ a complex inner product space (normed, with the Mathlib inner product structure). Given a homomorphism $\rho$ from $G$ to the multiplicative monoid of $\mathbb{C}$-linear endomorphisms of $L$, a submodule $S \le L$ with $\rho(x)f \in S$ for all $x \in G$ and $f \in S$, and a map $\iota : L \to H$ which is linear on $S$ in the sense that $\iota(a f + b g) = a\,\iota f + b\,\iota g$ for all $a,b \in \mathbb{C}$ and $f,g \in S$; suppose $c : G \to \mathbb{R}$ satisfies $c(x) > 0$ for all $x$ and $\|\iota(\rho(x)f)\|^2 = c(x)\,\|\iota f\|^2$ for all $x \in G$, $f \in S$. Suppose further given a predicate $P$ on $L$ and a map $E : L \to L$ which is likewise linear on $S$ for two-term combinations, such that $P(Ef)$ holds for every $f \in S$, and such that $\langle \iota(Ef), \iota g\rangle = \langle \iota f, \iota g \rangle$ whenever $f, g \in S$ and $P(g)$ holds. Let $\varphi, \varphi' \in S$ with $P(\varphi)$, and assume that for every $\varepsilon > 0$ there is $v$ in the $\mathbb{C}$-span of the orbit $\{\rho(x)\varphi : x \in G\}$ with $\|\iota\varphi' - \iota v\| < \varepsilon$. Let finally $W$ be a submodule of $L$ with $W \le S$, $W$ contained in the span of $\{\rho(x)\varphi' : x \in G\}$, $\rho(x)w \in W$ for all $x \in G$, $w \in W$, $Ew \in W$ for all $w \in W$, and $E(\rho(x)\varphi') \in W$ for all $x \in G$. Then for every $\varepsilon > 0$ there is $w \in W$ with $\|\iota\varphi' - \iota w\| < \varepsilon$.
--
--   This is the inner-product-space skeleton of the statement that a vector lying in the closure of the cyclic span of a vector $\varphi$ satisfying an invariance property $P$ is approximated, in the norm of $H$, by elements of a $\rho$- and $E$-stable subspace $W$ of the span of its own orbit; here $E$ plays the role of an averaging (projection-like) operator, symmetric against $P$-vectors, and $\rho$ acts by similitudes of the norm. It is used in the automorphic setting, for translation averages over a compact open subgroup, by [`AutomorphicForm.exists_levelInvariant_finTranslateSum_ne_zero_and_dense_of_isInTranslateSpanOn_of_finite`](thm.html#AutomorphicForm.exists_levelInvariant_finTranslateSum_ne_zero_and_dense_of_isInTranslateSpanOn_of_finite).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_InnerProductSpace_exists_mem_norm_sub_lt_of_exists_mem_span_orbit_of_average.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped InnerProductSpace

theorem InnerProductSpace.exists_mem_norm_sub_lt_of_exists_mem_span_orbit_of_average
    {G : Type*} [Group G] {L : Type*} [AddCommGroup L] [Module ℂ L]
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (ρ : G →* (L →ₗ[ℂ] L)) (S : Submodule ℂ L) (hS : ∀ x : G, ∀ f ∈ S, ρ x f ∈ S)
    (ι : L → H)
    (hι : ∀ (a b : ℂ) (f g : L), f ∈ S → g ∈ S → ι (a • f + b • g) = a • ι f + b • ι g)
    (c : G → ℝ) (hc : ∀ x, 0 < c x)
    (hρ : ∀ x : G, ∀ f ∈ S, ‖ι (ρ x f)‖ ^ 2 = c x * ‖ι f‖ ^ 2)
    (P : L → Prop) (E : L → L)
    (hE : ∀ (a b : ℂ) (f g : L), f ∈ S → g ∈ S → E (a • f + b • g) = a • E f + b • E g)
    (hEP : ∀ f ∈ S, P (E f))
    (hEinner : ∀ f ∈ S, ∀ g ∈ S, P g → ⟪ι (E f), ι g⟫_ℂ = ⟪ι f, ι g⟫_ℂ)
    (φ φ' : L) (hφ : φ ∈ S) (hPφ : P φ) (hφ' : φ' ∈ S)
    (hspan : ∀ ε : ℝ, 0 < ε →
      ∃ v ∈ Submodule.span ℂ (Set.range fun x : G => ρ x φ), ‖ι φ' - ι v‖ < ε)
    (W : Submodule ℂ L) (hWS : W ≤ S)
    (hWφ' : W ≤ Submodule.span ℂ (Set.range fun x : G => ρ x φ'))
    (hWρ : ∀ x : G, ∀ w ∈ W, ρ x w ∈ W) (hWE : ∀ w ∈ W, E w ∈ W)
    (hEφ' : ∀ x : G, E (ρ x φ') ∈ W) :
    ∀ ε : ℝ, 0 < ε → ∃ w ∈ W, ‖ι φ' - ι w‖ < ε := by sorry
