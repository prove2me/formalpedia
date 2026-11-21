-- Prove2me | Theorems.Thm_MasulloGRH_strictLF_quotient_condM_of_quotient_regular
-- name    : MasulloGRH.strictLF_quotient_condM_of_quotient_regular
-- status  : Proved
-- author  : @Ismael Correa
-- created : 2026-11-21T00:01:17.952184+00:00
-- url     : https://prove2.me/theorems/f4cf2be1-1d5c-4d57-aee7-761f3b6b0da9
-- title:
--   Regular quotient spectrum of a strict nuclear LF-space satisfies condition (M)
-- statement:
--   Let $E=\bigcup_m E_m$ be a strict countable locally convex inductive limit of nuclear Fréchet spaces $E_0\subseteq E_1\subseteq\cdots$ (each $E_m$ carries the topology induced by $E$, and $E$ carries the finest locally convex topology making all inclusions $E_m\hookrightarrow E$ continuous). Let $F\subseteq E$ be a closed linear subspace, $q\colon E\to E/F$ the quotient map, and $P_m=E_m/(F\cap E_m)$ with the quotient topology of $E_m$, with the natural continuous linear injections $\iota_m\colon P_m\to E/F$.
--
--   Assume the quotient is **regular with respect to the steps $P_m$**: every bounded $B\subseteq E/F$ is contained in $\iota_m(A)$ for some $m$ and some bounded $A\subseteq P_m$. Then the quotient spectrum $(P_m)$ satisfies **Retakh's condition (M) for the quotient spectrum $(P_m)$**, written in terms of the steps $E_m$:
--
--   $$\forall n\ \exists m\ge n\ \exists U\in\mathcal U_0(E_n)\ \forall k\ge m\ \forall W\in\mathcal U_0(E_m)\ \exists W'\in\mathcal U_0(E_k):\quad q(U)\cap q(W')\subseteq q(W).$$
--
--   This is the implication *regular $\Rightarrow$ (M)* for inductive spectra of Fréchet–Montel (here nuclear Fréchet, hence Fréchet–Schwartz) spaces: the steps $P_m$ are quotients of nuclear Fréchet spaces by closed subspaces, hence nuclear Fréchet, and for such spectra regularity forces Retakh's condition (M) (Wengenroth, Cor. 3.4).
--
--   **Formalization note.** Condition (M) is written exactly as in `MasulloGRH.strictLF_quotient_regular_of_condM` ($q(x)\in q(W')$ for $x\in U$ is written as $x-y\in F$ for some $y\in W'$); the regularity hypothesis exactly as in `MasulloGRH.strictLF_subspace_bornological_of_quotient_regular`; the limit-subspace condition exactly as in `MasulloGRH.limit_subspace_of_bounded_lifting`.
-- source:
--   A. M. Masullo, The Music of the Primes, draft of 20 November 2026, https://math216.wordpress.com/wp-content/uploads/2026/11/the-music-of-the-primes.pdf, Appendix C, Theorem C.1.5.11 (pp. 667-668); J. Wengenroth, Acyclic inductive spectra of Fréchet spaces, Studia Math. 120 (1996), §3, Cor. 3.4, p. 254

import Definitions.Def_MasulloGRH_LocallyConvex

set_option autoImplicit false

namespace MasulloGRH

theorem strictLF_quotient_condM_of_quotient_regular
    (E : Type*) [AddCommGroup E] [Module ℂ E]
    [TopologicalSpace E] (X : ℕ → Submodule ℂ E) (hmono : Monotone X)
    (hexh : ∀ x : E, ∃ n, x ∈ X n) (hX : ∀ n, IsFrechet (X n) ∧ IsNuclear (X n))
    (htop : ‹TopologicalSpace E› =
      sInf {t | IsLocallyConvexTopology E t ∧ ∀ n, @Continuous (X n) E _ t Subtype.val})
    (V : Submodule ℂ E) (hV : IsClosed (V : Set E))
    (hreg : ∀ B : Set (E ⧸ V), Bornology.IsVonNBounded ℂ B →
      ∃ (n : ℕ) (A : Set (X n ⧸ V.comap (X n).subtype)), Bornology.IsVonNBounded ℂ A ∧
        B ⊆ Submodule.mapQ (V.comap (X n).subtype) V (X n).subtype le_rfl '' A) :
    ∀ n : ℕ, ∃ m : ℕ, n ≤ m ∧ ∃ U ∈ nhds (0 : X n), ∀ k : ℕ, m ≤ k →
      ∀ W ∈ nhds (0 : X m), ∃ W' ∈ nhds (0 : X k),
        ∀ x ∈ U, ∀ y ∈ W', ((x : E) - (y : E)) ∈ V → ∃ w ∈ W, ((x : E) - (w : E)) ∈ V := by sorry

end MasulloGRH
