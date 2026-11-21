-- Prove2me | Theorems.Thm_MasulloGRH_strictLF_quotient_regular_of_condM_of_localization
-- name    : MasulloGRH.strictLF_quotient_regular_of_condM_of_localization
-- status  : Proved
-- author  : @Ismael Correa
-- created : 2026-11-20T23:50:23.534586+00:00
-- url     : https://prove2.me/theorems/842e895e-4aab-4b96-8382-eb07c5f2846b
-- title:
--   Localization of (M) implies regularity of the quotient $E/F$
-- statement:
--   Let $E=\bigcup_n E_n$ be a strict countable locally convex inductive limit of nuclear Fréchet spaces $E_0\subseteq E_1\subseteq\cdots$ (each $E_n$ with the topology induced by $E$; $E$ with the finest locally convex topology making all inclusions continuous). Let $F\subseteq E$ be a closed linear subspace, $q\colon E\to E/F$ the quotient map (with the quotient topology) and $P_n=E_n/(F\cap E_n)$ the quotient steps. Here $\mathcal U_0(\cdot)$ denotes the filter of $0$-neighbourhoods.
--
--   Assume the localized form of Retakh's condition: for every $n$ there are $m\ge n$ and $U\in\mathcal U_0(E_n)$ such that the topology of $E/F$ and that of $P_m$ coincide at $0$ on $q(U)$:
--   $$\forall n\ \exists m\ge n\ \exists U\in\mathcal U_0(E_n)\ \forall W\in\mathcal U_0(E_m)\ \exists G\in\mathcal U_0(E/F):\quad q(U)\cap G\subseteq q(W).$$
--
--   Then $E/F$ is regular with respect to the steps $P_m$: every bounded $B\subseteq E/F$ is contained in $\iota_m(A)$ for some $m$ and some bounded $A\subseteq P_m$, where $\iota_m\colon P_m\to E/F$ is the natural injection. (Von Neumann boundedness throughout.) This is the second half of Retakh's theorem (Wengenroth, Theorem 6.4): closures of $q(U)$ in $E/F$ stay inside the Fréchet space $P_m$, and a Baire-category argument on bounded Banach disks absorbs every bounded set into one step, where it is bounded because the two topologies agree there.
-- source:
--   V. S. Retakh, Subspaces of a countable inductive limit, Soviet Math. Dokl. 11 (1970) 1384-1386; J. Wengenroth, Derived Functors in Functional Analysis, LNM 1810 (2003), Section 6.1, Theorem 6.4 and its proof; used in A. M. Masullo, The Music of the Primes, draft of 20 November 2026, Appendix C, Theorem C.1.5.11 and proof of Corollary C.1.5.13 (pp. 667-669)

import Definitions.Def_MasulloGRH_LocallyConvex

set_option autoImplicit false

namespace MasulloGRH

theorem strictLF_quotient_regular_of_condM_of_localization (E : Type*) [AddCommGroup E] [Module ℂ E]
    [TopologicalSpace E] (X : ℕ → Submodule ℂ E) (hmono : Monotone X)
    (hexh : ∀ x : E, ∃ n, x ∈ X n) (hX : ∀ n, IsFrechet (X n) ∧ IsNuclear (X n))
    (htop : ‹TopologicalSpace E› =
      sInf {t | IsLocallyConvexTopology E t ∧ ∀ n, @Continuous (X n) E _ t Subtype.val})
    (V : Submodule ℂ E) (hV : IsClosed (V : Set E))
    (hL : ∀ n : ℕ, ∃ m : ℕ, n ≤ m ∧ ∃ U ∈ nhds (0 : X n), ∀ W ∈ nhds (0 : X m),
      ∃ G ∈ nhds (0 : E ⧸ V), ∀ x ∈ U, Submodule.Quotient.mk (x : E) ∈ G →
        ∃ w ∈ W, ((x : E) - (w : E)) ∈ V) :
    ∀ B : Set (E ⧸ V), Bornology.IsVonNBounded ℂ B →
      ∃ (n : ℕ) (A : Set (X n ⧸ V.comap (X n).subtype)), Bornology.IsVonNBounded ℂ A ∧
        B ⊆ Submodule.mapQ (V.comap (X n).subtype) V (X n).subtype le_rfl '' A := by sorry

end MasulloGRH
