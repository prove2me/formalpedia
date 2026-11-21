-- Prove2me | Theorems.Thm_MasulloGRH_strictLF_quotient_regular_of_condM
-- name    : MasulloGRH.strictLF_quotient_regular_of_condM
-- status  : Proved
-- author  : @Ismael Correa
-- created : 2026-11-20T23:41:54.17944+00:00
-- url     : https://prove2.me/theorems/9c7c2eb1-7d26-4275-8451-920ae70c66df
-- title:
--   Retakh's condition (M) makes the quotient spectrum of a strict LF-space regular
-- statement:
--   Let $E=\bigcup_m E_m$ be a strict countable locally convex inductive limit of nuclear Fréchet spaces $E_0\subseteq E_1\subseteq\cdots$ (each $E_m$ carries the topology induced by $E$, and $E$ carries the finest locally convex topology making all inclusions $E_m\hookrightarrow E$ continuous). Let $F\subseteq E$ be a closed linear subspace, $q\colon E\to E/F$ the quotient map, and $P_m=E_m/(F\cap E_m)$ with the quotient topology of $E_m$; the natural maps $P_m\to P_k$ ($m\le k$) and $\iota_m\colon P_m\to E/F$ are continuous linear injections.
--
--   Assume the quotient spectrum $(P_m)$ satisfies **Retakh's condition (M) for the quotient spectrum $(P_m)$**, written in terms of the steps $E_m$ (neighbourhoods of $0$ in $P_m$ are exactly the sets containing the image of a $0$-neighbourhood of $E_m$):
--
--   $$\forall n\ \exists m\ge n\ \exists U\in\mathcal U_0(E_n)\ \forall k\ge m\ \forall W\in\mathcal U_0(E_m)\ \exists W'\in\mathcal U_0(E_k):\quad q(U)\cap q(W')\subseteq q(W).$$
--
--   In words: on the image of $U$ the topologies induced by all steps $P_k$, $k\ge m$, coincide (at $0$) with the topology of $P_m$. In Lean, $q(x)\in q(W')$ for $x\in U$ is written as: $x-y\in F$ for some $y\in W'$.
--
--   Then the quotient is **regular with respect to the steps $P_m$**: every bounded subset $B\subseteq E/F$ is contained in $\iota_m(A)$ for some $m$ and some bounded $A\subseteq P_m$:
--
--   $$\forall B\subseteq E/F\ \text{bounded}\quad\exists m,\ \exists A\subseteq P_m\ \text{bounded}:\quad B\subseteq\iota_m(A).$$
--
--   Here $E/F$ with the quotient topology is the locally convex inductive limit of the Fréchet spaces $P_m$, and this is Retakh's theorem that an LF-spectrum of Fréchet spaces satisfying (M) has a regular inductive limit. Boundedness is von Neumann boundedness.
-- source:
--   V. S. Retakh, Subspaces of a countable inductive limit, Soviet Math. Dokl. 11 (1970) 1384-1386; J. Wengenroth, Derived Functors in Functional Analysis, LNM 1810 (2003), Thm. 6.4; used in A. M. Masullo, The Music of the Primes, draft of 20 November 2026, Appendix C, Theorem C.1.5.11 and proof of Corollary C.1.5.13 (pp. 667-669)

import Definitions.Def_MasulloGRH_LocallyConvex

set_option autoImplicit false

namespace MasulloGRH

theorem strictLF_quotient_regular_of_condM (E : Type*) [AddCommGroup E] [Module ℂ E]
    [TopologicalSpace E] (X : ℕ → Submodule ℂ E) (hmono : Monotone X)
    (hexh : ∀ x : E, ∃ n, x ∈ X n) (hX : ∀ n, IsFrechet (X n) ∧ IsNuclear (X n))
    (htop : ‹TopologicalSpace E› =
      sInf {t | IsLocallyConvexTopology E t ∧ ∀ n, @Continuous (X n) E _ t Subtype.val})
    (V : Submodule ℂ E) (hV : IsClosed (V : Set E))
    (hM : ∀ n : ℕ, ∃ m : ℕ, n ≤ m ∧ ∃ U ∈ nhds (0 : X n), ∀ k : ℕ, m ≤ k →
      ∀ W ∈ nhds (0 : X m), ∃ W' ∈ nhds (0 : X k),
        ∀ x ∈ U, ∀ y ∈ W', ((x : E) - (y : E)) ∈ V → ∃ w ∈ W, ((x : E) - (w : E)) ∈ V) :
    ∀ B : Set (E ⧸ V), Bornology.IsVonNBounded ℂ B →
      ∃ (n : ℕ) (A : Set (X n ⧸ V.comap (X n).subtype)), Bornology.IsVonNBounded ℂ A ∧
        B ⊆ Submodule.mapQ (V.comap (X n).subtype) V (X n).subtype le_rfl '' A := by sorry

end MasulloGRH
