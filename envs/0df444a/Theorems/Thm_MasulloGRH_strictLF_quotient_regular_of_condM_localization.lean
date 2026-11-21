-- Prove2me | Theorems.Thm_MasulloGRH_strictLF_quotient_regular_of_condM_localization
-- name    : MasulloGRH.strictLF_quotient_regular_of_condM_localization
-- status  : Proved
-- author  : @Ismael Correa
-- created : 2026-11-20T23:50:23.466107+00:00
-- url     : https://prove2.me/theorems/11851e98-b600-455a-9ef7-ceb6cfdcb51b
-- title:
--   Retakh's localization lemma: (M) forces $E/F$ and $P_m$ to agree on $q(U)$
-- statement:
--   Let $E=\bigcup_n E_n$ be a strict countable locally convex inductive limit of nuclear Fréchet spaces $E_0\subseteq E_1\subseteq\cdots$ (each $E_n$ with the topology induced by $E$; $E$ with the finest locally convex topology making all inclusions continuous). Let $F\subseteq E$ be a closed linear subspace, $q\colon E\to E/F$ the quotient map (with the quotient topology) and $P_n=E_n/(F\cap E_n)$ the quotient steps. Here $\mathcal U_0(\cdot)$ denotes the filter of $0$-neighbourhoods.
--
--   Assume the quotient spectrum $(P_m)$ satisfies Retakh's condition (M), written in terms of the steps:
--   $$\forall n\ \exists m\ge n\ \exists U\in\mathcal U_0(E_n)\ \forall k\ge m\ \forall W\in\mathcal U_0(E_m)\ \exists W'\in\mathcal U_0(E_k):\quad q(U)\cap q(W')\subseteq q(W).$$
--
--   Then (M) localizes to the inductive limit itself (Retakh's lemma): on $q(U)$ the quotient topology of $E/F$ and the topology of $P_m$ coincide at $0$,
--   $$\forall n\ \exists m\ge n\ \exists U\in\mathcal U_0(E_n)\ \forall W\in\mathcal U_0(E_m)\ \exists G\in\mathcal U_0(E/F):\quad q(U)\cap G\subseteq q(W).$$
--
--   In Lean, $q(x)\in q(W)$ for $x\in U$ is written as $x-w\in F$ for some $w\in W$. This is the key step of Retakh's theorem (Wengenroth, proof of Theorem 6.4): the absolutely convex hull of a suitable union of the neighbourhoods $W'$ provided by (M) is a $0$-neighbourhood of the inductive limit $E/F=\operatorname{ind}P_m$.
-- source:
--   V. S. Retakh, Subspaces of a countable inductive limit, Soviet Math. Dokl. 11 (1970) 1384-1386; J. Wengenroth, Derived Functors in Functional Analysis, LNM 1810 (2003), Section 6.1, Theorem 6.4 and its proof; used in A. M. Masullo, The Music of the Primes, draft of 20 November 2026, Appendix C, Theorem C.1.5.11 and proof of Corollary C.1.5.13 (pp. 667-669)

import Definitions.Def_MasulloGRH_LocallyConvex

set_option autoImplicit false

namespace MasulloGRH

theorem strictLF_quotient_regular_of_condM_localization (E : Type*) [AddCommGroup E] [Module ℂ E]
    [TopologicalSpace E] (X : ℕ → Submodule ℂ E) (hmono : Monotone X)
    (hexh : ∀ x : E, ∃ n, x ∈ X n) (hX : ∀ n, IsFrechet (X n) ∧ IsNuclear (X n))
    (htop : ‹TopologicalSpace E› =
      sInf {t | IsLocallyConvexTopology E t ∧ ∀ n, @Continuous (X n) E _ t Subtype.val})
    (V : Submodule ℂ E) (hV : IsClosed (V : Set E))
    (hM : ∀ n : ℕ, ∃ m : ℕ, n ≤ m ∧ ∃ U ∈ nhds (0 : X n), ∀ k : ℕ, m ≤ k →
      ∀ W ∈ nhds (0 : X m), ∃ W' ∈ nhds (0 : X k),
        ∀ x ∈ U, ∀ y ∈ W', ((x : E) - (y : E)) ∈ V → ∃ w ∈ W, ((x : E) - (w : E)) ∈ V) :
    ∀ n : ℕ, ∃ m : ℕ, n ≤ m ∧ ∃ U ∈ nhds (0 : X n), ∀ W ∈ nhds (0 : X m),
      ∃ G ∈ nhds (0 : E ⧸ V), ∀ x ∈ U, Submodule.Quotient.mk (x : E) ∈ G →
        ∃ w ∈ W, ((x : E) - (w : E)) ∈ V := by sorry

end MasulloGRH
