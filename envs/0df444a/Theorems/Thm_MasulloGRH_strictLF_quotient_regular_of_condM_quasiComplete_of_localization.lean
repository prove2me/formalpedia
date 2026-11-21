-- Prove2me | Theorems.Thm_MasulloGRH_strictLF_quotient_regular_of_condM_quasiComplete_of_localization
-- name    : MasulloGRH.strictLF_quotient_regular_of_condM_quasiComplete_of_localization
-- status  : Proved
-- author  : @Ismael Correa
-- created : 2026-11-20T23:56:02.237649+00:00
-- url     : https://prove2.me/theorems/67e4edc0-c5a6-4160-b43a-75821b7fee2c
-- title:
--   Localized condition (M) makes the quotient $E/F$ quasi-complete
-- statement:
--   Let $E=\bigcup_n E_n$ be a strict countable locally convex inductive limit of nuclear Fréchet spaces $E_0\subseteq E_1\subseteq\cdots$ (each $E_n$ with the topology induced by $E$; $E$ with the finest locally convex topology making all inclusions continuous). Let $F\subseteq E$ be a closed linear subspace, $q\colon E\to E/F$ the quotient map (with the quotient topology) and $P_n=E_n/(F\cap E_n)$ the quotient steps, with natural continuous injections $\iota_n\colon P_n\to E/F$. Here $\mathcal U_0(\cdot)$ denotes the filter of $0$-neighbourhoods.
--
--   Assume the localized form of Retakh's condition (M): for every $n$ there are $m\ge n$ and $U\in\mathcal U_0(E_n)$ on whose image the topologies of $E/F$ and of $P_m$ coincide at $0$,
--   $$\forall n\ \exists m\ge n\ \exists U\in\mathcal U_0(E_n)\ \forall W\in\mathcal U_0(E_m)\ \exists G\in\mathcal U_0(E/F):\quad q(U)\cap G\subseteq q(W).$$
--
--   Then the quotient $E/F=\operatorname{ind}P_m$ is quasi-complete: it is Hausdorff and every bounded Cauchy filter on $E/F$ converges.
--
--   This is the completeness half of the Retakh–Palamodov theory: an LF-spectrum of Fréchet spaces satisfying (M) has a complete inductive limit.
-- source:
--   J. Wengenroth, Derived Functors in Functional Analysis, LNM 1810 (2003), Section 6.1 (Theorem 6.4: LF-spectra satisfying (M) have complete inductive limits); D. Vogt, Regularity properties of (LF)-spaces, in: Progress in Functional Analysis (1992), 57-84; used in A. M. Masullo, The Music of the Primes, draft of 20 November 2026, Appendix C, Theorem C.1.5.11 (pp. 667-669)

import Definitions.Def_MasulloGRH_LocallyConvex

set_option autoImplicit false

namespace MasulloGRH

theorem strictLF_quotient_regular_of_condM_quasiComplete_of_localization (E : Type*) [AddCommGroup E] [Module ℂ E]
    [TopologicalSpace E] (X : ℕ → Submodule ℂ E) (hmono : Monotone X)
    (hexh : ∀ x : E, ∃ n, x ∈ X n) (hX : ∀ n, IsFrechet (X n) ∧ IsNuclear (X n))
    (htop : ‹TopologicalSpace E› =
      sInf {t | IsLocallyConvexTopology E t ∧ ∀ n, @Continuous (X n) E _ t Subtype.val})
    (V : Submodule ℂ E) (hV : IsClosed (V : Set E))
    (hL : ∀ n : ℕ, ∃ m : ℕ, n ≤ m ∧ ∃ U ∈ nhds (0 : X n), ∀ W ∈ nhds (0 : X m),
      ∃ G ∈ nhds (0 : E ⧸ V), ∀ x ∈ U, Submodule.Quotient.mk (x : E) ∈ G →
        ∃ w ∈ W, ((x : E) - (w : E)) ∈ V) :
    IsQuasiComplete (E ⧸ V) := by sorry

end MasulloGRH
