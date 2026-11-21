-- Prove2me | Theorems.Thm_MasulloGRH_strictLF_quotient_condM_of_limit_subspace
-- name    : MasulloGRH.strictLF_quotient_condM_of_limit_subspace
-- status  : Proved
-- author  : @Ismael Correa
-- created : 2026-11-20T23:42:10.56145+00:00
-- url     : https://prove2.me/theorems/8f11720e-5858-4f55-b3ce-860751e06570
-- title:
--   Limit subspaces of strict LF-spaces give quotient spectra satisfying Retakh's condition (M)
-- statement:
--   Let $E=\bigcup_m E_m$ be a strict countable locally convex inductive limit of nuclear Fréchet spaces $E_0\subseteq E_1\subseteq\cdots$ (each $E_m$ carries the topology induced by $E$, and $E$ carries the finest locally convex topology making all inclusions $E_m\hookrightarrow E$ continuous). Let $F\subseteq E$ be a closed linear subspace, $q\colon E\to E/F$ the quotient map, and $P_m=E_m/(F\cap E_m)$ with the quotient topology of $E_m$; the natural maps $P_m\to P_k$ ($m\le k$) and $\iota_m\colon P_m\to E/F$ are continuous linear injections.
--
--   Assume $F$ is a **limit subspace**: the topology induced on $F$ by $E$ equals the locally convex inductive limit topology of the subspaces $F\cap E_m$ (each with the topology induced from $E$). Then the quotient spectrum $(P_m)$ satisfies **Retakh's condition (M) for the quotient spectrum $(P_m)$**, written in terms of the steps $E_m$ (neighbourhoods of $0$ in $P_m$ are exactly the sets containing the image of a $0$-neighbourhood of $E_m$):
--
--   $$\forall n\ \exists m\ge n\ \exists U\in\mathcal U_0(E_n)\ \forall k\ge m\ \forall W\in\mathcal U_0(E_m)\ \exists W'\in\mathcal U_0(E_k):\quad q(U)\cap q(W')\subseteq q(W).$$
--
--   In words: on the image of $U$ the topologies induced by all steps $P_k$, $k\ge m$, coincide (at $0$) with the topology of $P_m$. In Lean, $q(x)\in q(W')$ for $x\in U$ is written as: $x-y\in F$ for some $y\in W'$.
--
--   Proof idea: the rows $0\to\bigoplus F_m\to\bigoplus E_m\to\bigoplus P_m\to0$ are topologically exact; the strict spectra $(F\cap E_m)$ and $(E_m)$ are acyclic, and since $F$ carries the inductive limit topology the map $\bigoplus_m F\cap E_m\to F$ is open, which by a diagram chase makes the map $\sigma$ of Definition C.1.5.8 for $(P_m)$ a topological embedding with closed range, i.e. $(P_m)$ is acyclic. For spectra of Fréchet spaces acyclicity is equivalent to condition (M) (Retakh, Palamodov, Vogt; see Wengenroth).
-- source:
--   A. M. Masullo, The Music of the Primes, draft of 20 November 2026, https://math216.wordpress.com/wp-content/uploads/2026/11/the-music-of-the-primes.pdf, Appendix C, Definitions C.1.5.6, C.1.5.8 and Theorem C.1.5.11 (pp. 666-668); J. Wengenroth, Acyclic inductive spectra of Fréchet spaces, Studia Math. 120 (1996), §3 (Cor. 3.4, p. 254); V. S. Retakh, Subspaces of a countable inductive limit, Soviet Math. Dokl. 11 (1970); D. Vogt, Regularity properties of (LF)-spaces (1992), Thm. 2.7

import Definitions.Def_MasulloGRH_LocallyConvex

set_option autoImplicit false

namespace MasulloGRH

theorem strictLF_quotient_condM_of_limit_subspace (E : Type*) [AddCommGroup E] [Module ℂ E]
    [TopologicalSpace E] (X : ℕ → Submodule ℂ E) (hmono : Monotone X)
    (hexh : ∀ x : E, ∃ n, x ∈ X n) (hX : ∀ n, IsFrechet (X n) ∧ IsNuclear (X n))
    (htop : ‹TopologicalSpace E› =
      sInf {t | IsLocallyConvexTopology E t ∧ ∀ n, @Continuous (X n) E _ t Subtype.val})
    (V : Submodule ℂ E) (hV : IsClosed (V : Set E))
    (hlim : (instTopologicalSpaceSubtype : TopologicalSpace V) =
        sInf {t | IsLocallyConvexTopology V t ∧
          ∀ n, @Continuous ↥(V ⊓ X n) V _ t (Submodule.inclusion inf_le_left)}) :
    ∀ n : ℕ, ∃ m : ℕ, n ≤ m ∧ ∃ U ∈ nhds (0 : X n), ∀ k : ℕ, m ≤ k →
      ∀ W ∈ nhds (0 : X m), ∃ W' ∈ nhds (0 : X k),
        ∀ x ∈ U, ∀ y ∈ W', ((x : E) - (y : E)) ∈ V → ∃ w ∈ W, ((x : E) - (w : E)) ∈ V := by sorry

end MasulloGRH
