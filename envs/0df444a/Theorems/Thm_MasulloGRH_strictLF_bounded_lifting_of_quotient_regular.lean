-- Prove2me | Theorems.Thm_MasulloGRH_strictLF_bounded_lifting_of_quotient_regular
-- name    : MasulloGRH.strictLF_bounded_lifting_of_quotient_regular
-- status  : Proved
-- author  : @Ismael Correa
-- created : 2026-11-20T23:20:55.688204+00:00
-- url     : https://prove2.me/theorems/5e58881d-4347-4a70-b0c8-342a796c8544
-- title:
--   Regularity of the quotient steps gives the bounded lifting property
-- statement:
--   Let $E$ be a strict countable locally convex inductive limit of nuclear Fréchet spaces: $E=\bigcup_m E_m$ for an increasing sequence of subspaces $E_0\subseteq E_1\subseteq\cdots$, each a nuclear Fréchet space for the topology induced by $E$, and $E$ carries the finest locally convex topology for which all inclusions $E_m\hookrightarrow E$ are continuous. Let $F\subseteq E$ be a closed linear subspace, $q\colon E\to E/F$ the quotient map, and for each $m$ let $P_m=E_m/(F\cap E_m)$ with the quotient topology of $E_m$, together with the natural continuous linear injection $\iota_m\colon P_m\to E/F$.
--
--   Assume the quotient is **regular with respect to the steps $P_m$**: every bounded subset $B\subseteq E/F$ is contained in $\iota_m(A)$ for some $m$ and some bounded subset $A\subseteq P_m$. Then $q\colon E\to E/F$ has the **bounded lifting property**: every bounded subset $B\subseteq E/F$ is contained in $q(B')$ for some bounded subset $B'\subseteq E$.
--
--   This is the lifting step in the proof of Corollary C.1.5.13: a bounded set of $P_m$ lifts to a bounded set of the nuclear (hence Schwartz) Fréchet space $E_m$ by Grothendieck's lifting theorem for quotients of Fréchet–Schwartz spaces, and its image in $E$ is bounded.
--
--   **Formalization Note** The step $P_m$ is the Lean quotient `X m ⧸ V.comap (X m).subtype` and $\iota_m$ is `Submodule.mapQ (V.comap (X m).subtype) V (X m).subtype le_rfl`; boundedness is von Neumann boundedness. The limit-subspace condition is written exactly as in `MasulloGRH.limit_subspace_iff_bounded_lifting`.
-- source:
--   A. M. Masullo, The Music of the Primes, draft of 20 November 2026, https://math216.wordpress.com/wp-content/uploads/2026/11/the-music-of-the-primes.pdf, Appendix C, Theorem C.1.5.11 (pp. 667-668) and the proof of Corollary C.1.5.13 (pp. 668-669); J. Wengenroth, Acyclic inductive spectra of Fréchet spaces, Studia Math. 120 (1996), §3, Cor. 3.4, p. 254

import Definitions.Def_MasulloGRH_LocallyConvex

set_option autoImplicit false

namespace MasulloGRH

theorem strictLF_bounded_lifting_of_quotient_regular (E : Type*) [AddCommGroup E] [Module ℂ E]
    [TopologicalSpace E] (X : ℕ → Submodule ℂ E) (hmono : Monotone X)
    (hexh : ∀ x : E, ∃ n, x ∈ X n) (hX : ∀ n, IsFrechet (X n) ∧ IsNuclear (X n))
    (htop : ‹TopologicalSpace E› =
      sInf {t | IsLocallyConvexTopology E t ∧ ∀ n, @Continuous (X n) E _ t Subtype.val})
    (V : Submodule ℂ E) (hV : IsClosed (V : Set E))
    (hreg : ∀ B : Set (E ⧸ V), Bornology.IsVonNBounded ℂ B →
      ∃ (n : ℕ) (A : Set (X n ⧸ V.comap (X n).subtype)), Bornology.IsVonNBounded ℂ A ∧
        B ⊆ Submodule.mapQ (V.comap (X n).subtype) V (X n).subtype le_rfl '' A) :
    LiftsBoundedSets (V.mkQ : E → E ⧸ V) := by sorry

end MasulloGRH
