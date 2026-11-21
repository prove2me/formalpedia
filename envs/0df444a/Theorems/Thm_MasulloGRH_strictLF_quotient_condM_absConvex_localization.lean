-- Prove2me | Theorems.Thm_MasulloGRH_strictLF_quotient_condM_absConvex_localization
-- name    : MasulloGRH.strictLF_quotient_condM_absConvex_localization
-- status  : Proved
-- author  : @Ismael Correa
-- created : 2026-11-21T00:08:16.05054+00:00
-- url     : https://prove2.me/theorems/b1086e61-79c9-43f4-8d11-4f61c0314aea
-- title:
--   Retakh's lemma for the quotient spectrum: condition (M) gives absolutely convex localizing sets
-- statement:
--   Let $E=\bigcup_n X_n$ be a strict LF-space of nuclear Fréchet spaces over $\mathbb C$ (the steps $X_n$ carry the topology induced by $E$) and let $V\subseteq E$ be a closed subspace. Assume the quotient spectrum $X_k/(V\cap X_k)$ satisfies Retakh's condition (M) in the following form: for every $n$ there are $m\ge n$ and a $0$-neighbourhood $U$ of $X_n$ such that for all $k\ge m$ and every $0$-neighbourhood $W$ of $X_m$ there is a $0$-neighbourhood $W'$ of $X_k$ with
--   $$U\cap (W'+V)\subseteq W+V.$$
--   Then for every $n$ there are $m\ge n$ and a $0$-neighbourhood $U$ of $X_n$ such that for every $0$-neighbourhood $W$ of $X_m$ there is an absolutely convex set $\Omega\subseteq E$ whose trace $\Omega\cap X_k$ is a $0$-neighbourhood of $X_k$ for every $k$, and
--   $$U\cap(\Omega+V)\subseteq W+V.$$
--
--   This is the combinatorial core of Retakh's theorem that (M) implies that the inductive limit topology and the step topology of $X_m/(V\cap X_m)$ coincide on the image of $U$ (the set $\Omega$ is built as an absolutely convex hull of suitably chosen step neighbourhoods).
-- source:
--   A. M. Masullo, The Music of the Primes (draft 20 Nov 2026), Appendix C, §C.1.5; V. S. Retakh, Subspaces of a countable inductive limit, Soviet Math. Dokl. 11 (1970); J. Wengenroth, Derived Functors in Functional Analysis, LNM 1810, Ch. 6.

import Definitions.Def_MasulloGRH_LocallyConvex

set_option autoImplicit false

namespace MasulloGRH

theorem strictLF_quotient_condM_absConvex_localization (E : Type*) [AddCommGroup E] [Module ℂ E]
    [TopologicalSpace E] (X : ℕ → Submodule ℂ E) (hmono : Monotone X)
    (hexh : ∀ x : E, ∃ n, x ∈ X n) (hX : ∀ n, IsFrechet (X n) ∧ IsNuclear (X n))
    (htop : ‹TopologicalSpace E› =
      sInf {t | IsLocallyConvexTopology E t ∧ ∀ n, @Continuous (X n) E _ t Subtype.val})
    (V : Submodule ℂ E) (hV : IsClosed (V : Set E))
    (hM : ∀ n : ℕ, ∃ m : ℕ, n ≤ m ∧ ∃ U ∈ nhds (0 : X n), ∀ k : ℕ, m ≤ k →
      ∀ W ∈ nhds (0 : X m), ∃ W' ∈ nhds (0 : X k),
        ∀ x ∈ U, ∀ y ∈ W', ((x : E) - (y : E)) ∈ V → ∃ w ∈ W, ((x : E) - (w : E)) ∈ V) :
    ∀ n : ℕ, ∃ m : ℕ, n ≤ m ∧ ∃ U ∈ nhds (0 : X n), ∀ W ∈ nhds (0 : X m),
      ∃ Ω : Set E, Convex ℝ Ω ∧ Balanced ℂ Ω ∧
        (∀ k, ((↑) : X k → E) ⁻¹' Ω ∈ nhds (0 : X k)) ∧
        ∀ x ∈ U, ∀ y ∈ Ω, ((x : E) - y) ∈ V → ∃ w ∈ W, ((x : E) - (w : E)) ∈ V := by sorry

end MasulloGRH
