-- Prove2me | Theorems.Thm_MasulloGRH_strictLF_quotient_regular_of_bounded_lifting
-- name    : MasulloGRH.strictLF_quotient_regular_of_bounded_lifting
-- status  : Proved
-- author  : @Ismael Correa
-- created : 2026-11-20T23:44:05.647793+00:00
-- url     : https://prove2.me/theorems/b75600d1-1332-44b1-b24c-65aea5a54ece
-- title:
--   Bounded lifting makes the quotient spectrum of a strict nuclear LF-space regular
-- statement:
--   Let $E$ be a strict countable locally convex inductive limit of nuclear Fréchet spaces: $E=\bigcup_m E_m$ for an increasing sequence of subspaces $E_0\subseteq E_1\subseteq\cdots$, each a nuclear Fréchet space for the topology induced by $E$, and $E$ carries the finest locally convex topology for which all inclusions $E_m\hookrightarrow E$ are continuous. Let $F\subseteq E$ be a closed linear subspace, $q\colon E\to E/F$ the quotient map, and for each $m$ let $P_m=E_m/(F\cap E_m)$ with the quotient topology of $E_m$, together with the natural continuous linear injection $\iota_m\colon P_m\to E/F$.
--
--   Assume $q\colon E\to E/F$ has the **bounded lifting property**: every bounded subset of $E/F$ is contained in $q(B')$ for a bounded $B'\subseteq E$. Then the quotient is **regular with respect to the steps $P_m$**: every bounded $B\subseteq E/F$ is contained in $\iota_m(A)$ for some $m$ and some bounded $A\subseteq P_m$.
--
--   Proof idea: a bounded $B'\subseteq E$ lies and is bounded in some step $E_m$ (bounded sets of strict LF-spaces are localized), and its image in $P_m$ is bounded since $E_m\to P_m$ is continuous and linear; since $\iota_m\circ(E_m\to P_m)=q|_{E_m}$, the image covers $B$. This is the first step of the implication (2)$\Rightarrow$(1) of Theorem C.1.5.11, converse to `MasulloGRH.strictLF_bounded_lifting_of_quotient_regular`.
--
--   **Formalization Note** The step $P_m$ is the Lean quotient `X m ⧸ V.comap (X m).subtype` and $\iota_m$ is `Submodule.mapQ (V.comap (X m).subtype) V (X m).subtype le_rfl`; boundedness is von Neumann boundedness; `IsBornological` is the predicate of `Definitions.Def_MasulloGRH_LocallyConvex` (every seminorm bounded on bounded sets is continuous). The limit-subspace condition is written exactly as in `MasulloGRH.limit_subspace_iff_bounded_lifting`.
-- source:
--   A. M. Masullo, The Music of the Primes, draft of 20 November 2026, https://math216.wordpress.com/wp-content/uploads/2026/11/the-music-of-the-primes.pdf, Appendix C, Theorem C.1.5.11 (pp. 667-668); J. Wengenroth, Acyclic inductive spectra of Fréchet spaces, Studia Math. 120 (1996), §3, Cor. 3.4, p. 254

import Definitions.Def_MasulloGRH_LocallyConvex

set_option autoImplicit false

namespace MasulloGRH

theorem strictLF_quotient_regular_of_bounded_lifting
    (E : Type*) [AddCommGroup E] [Module ℂ E]
    [TopologicalSpace E] (X : ℕ → Submodule ℂ E) (hmono : Monotone X)
    (hexh : ∀ x : E, ∃ n, x ∈ X n) (hX : ∀ n, IsFrechet (X n) ∧ IsNuclear (X n))
    (htop : ‹TopologicalSpace E› =
      sInf {t | IsLocallyConvexTopology E t ∧ ∀ n, @Continuous (X n) E _ t Subtype.val})
    (V : Submodule ℂ E) (hV : IsClosed (V : Set E))
    (hlift : LiftsBoundedSets (V.mkQ : E → E ⧸ V)) :
    ∀ B : Set (E ⧸ V), Bornology.IsVonNBounded ℂ B →
      ∃ (n : ℕ) (A : Set (X n ⧸ V.comap (X n).subtype)), Bornology.IsVonNBounded ℂ A ∧
        B ⊆ Submodule.mapQ (V.comap (X n).subtype) V (X n).subtype le_rfl '' A := by sorry

end MasulloGRH
