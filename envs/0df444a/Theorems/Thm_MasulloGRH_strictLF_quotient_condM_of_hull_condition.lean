-- Prove2me | Theorems.Thm_MasulloGRH_strictLF_quotient_condM_of_hull_condition
-- name    : MasulloGRH.strictLF_quotient_condM_of_hull_condition
-- status  : Proved
-- author  : @Ismael Correa
-- created : 2026-11-20T23:55:50.27871+00:00
-- url     : https://prove2.me/theorems/068ce4b5-b7dd-4759-bafa-eee1d2929c2f
-- title:
--   The hull condition implies Retakh's condition (M) for the quotient spectrum
-- statement:
--   Let $E=\bigcup_k E_k$ be a strict countable locally convex inductive limit of nuclear Fréchet spaces (each $E_k$ with the topology induced by $E$, $E$ with the finest locally convex topology making all inclusions continuous), and let $F\subseteq E$ be a closed subspace. Write $\Gamma(S)=\operatorname{conv}_{\mathbb R}(\operatorname{bal}_{\mathbb C}S)$ and assume the **hull condition**: for every sequence $(W_k)$ of $0$-neighbourhoods $W_k\subseteq E_k$ there is a sequence $(O_k)$ of $0$-neighbourhoods $O_k\subseteq E_k$ with
--   $$F\cap\Gamma\Big(\bigcup_k O_k\Big)\subseteq\Gamma\Big(\bigcup_k (W_k\cap F)\Big).$$
--   (Since the sets $\Gamma(\bigcup_k O_k)$ form a $0$-basis of $E$, this condition is equivalent to $F$ being a limit subspace.)
--
--   Then the quotient spectrum $P_m=E_m/(F\cap E_m)$ satisfies Retakh's condition (M), written in terms of the steps:
--   $$\forall n\ \exists m\ge n\ \exists U\in\mathcal U_0(E_n)\ \forall k\ge m\ \forall W\in\mathcal U_0(E_m)\ \exists W'\in\mathcal U_0(E_k):\quad q(U)\cap q(W')\subseteq q(W),$$
--   where $q\colon E\to E/F$; in Lean, $q(x)\in q(W')$ for $x\in U$ reads: $x-y\in F$ for some $y\in W'$.
--
--   This is Retakh's theorem (limit subspace $\Rightarrow$ (M)); one proof shows that the quotient spectrum is acyclic by a diagram chase on $0\to\bigoplus F\cap E_m\to\bigoplus E_m\to\bigoplus P_m\to 0$, and then uses that acyclic Fréchet spectra satisfy (M) (Retakh, Palamodov, Vogt, Wengenroth).
-- source:
--   A. M. Masullo, The Music of the Primes (draft 20 Nov 2026), Appendix C, Definition C.1.5.8 and Theorem C.1.5.11 (pp. 667-669); V. S. Retakh, Subspaces of a countable inductive limit, Soviet Math. Dokl. 11 (1970); J. Wengenroth, Acyclic inductive spectra of Fréchet spaces, Studia Math. 120 (1996).

import Definitions.Def_MasulloGRH_LocallyConvex

set_option autoImplicit false

namespace MasulloGRH

theorem strictLF_quotient_condM_of_hull_condition (E : Type*) [AddCommGroup E] [Module ℂ E]
    [TopologicalSpace E] (X : ℕ → Submodule ℂ E) (hmono : Monotone X)
    (hexh : ∀ x : E, ∃ n, x ∈ X n) (hX : ∀ n, IsFrechet (X n) ∧ IsNuclear (X n))
    (htop : ‹TopologicalSpace E› =
      sInf {t | IsLocallyConvexTopology E t ∧ ∀ n, @Continuous (X n) E _ t Subtype.val})
    (V : Submodule ℂ E) (hV : IsClosed (V : Set E))
    (hhull : ∀ W : ∀ k, Set (X k), (∀ k, W k ∈ nhds (0 : X k)) →
      ∃ O : ∀ k, Set (X k), (∀ k, O k ∈ nhds (0 : X k)) ∧
        ∀ v ∈ V, v ∈ convexHull ℝ (balancedHull ℂ (⋃ k, Subtype.val '' O k)) →
          v ∈ convexHull ℝ (balancedHull ℂ (⋃ k, (Subtype.val '' W k) ∩ (V : Set E)))) :
    ∀ n : ℕ, ∃ m : ℕ, n ≤ m ∧ ∃ U ∈ nhds (0 : X n), ∀ k : ℕ, m ≤ k →
      ∀ W ∈ nhds (0 : X m), ∃ W' ∈ nhds (0 : X k),
        ∀ x ∈ U, ∀ y ∈ W', ((x : E) - (y : E)) ∈ V → ∃ w ∈ W, ((x : E) - (w : E)) ∈ V := by sorry

end MasulloGRH
