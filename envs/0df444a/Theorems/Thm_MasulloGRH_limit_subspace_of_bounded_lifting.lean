-- Prove2me | Theorems.Thm_MasulloGRH_limit_subspace_of_bounded_lifting
-- name    : MasulloGRH.limit_subspace_of_bounded_lifting
-- status  : Proved
-- author  : @Ismael Correa
-- created : 2026-11-20T23:20:52.078592+00:00
-- url     : https://prove2.me/theorems/09fffa70-ef75-4314-b678-163419c65913
-- title:
--   Bounded lifting implies limit subspace in strict LF-spaces of nuclear Fréchet spaces
-- statement:
--   Let $E$ be a strict countable locally convex inductive limit of nuclear Fréchet spaces: $E=\bigcup_m E_m$ for an increasing sequence of subspaces $E_0\subseteq E_1\subseteq\cdots$, each a nuclear Fréchet space for the topology induced by $E$, and $E$ carries the finest locally convex topology for which all inclusions $E_m\hookrightarrow E$ are continuous. Let $F\subseteq E$ be a closed linear subspace, $q\colon E\to E/F$ the quotient map, and for each $m$ let $P_m=E_m/(F\cap E_m)$ with the quotient topology of $E_m$, together with the natural continuous linear injection $\iota_m\colon P_m\to E/F$.
--
--   Assume $q\colon E\to E/F$ has the bounded lifting property: every bounded subset of $E/F$ is contained in $q(B')$ for some bounded $B'\subseteq E$. Then $F$ is a **limit subspace**: the topology induced on $F$ by $E$ equals the locally convex inductive limit topology of the subspaces $F\cap E_m$, each with the topology induced from $E$ (equivalently from $E_m$).
--
--   This is the implication (2) $\Rightarrow$ (1) of Theorem C.1.5.11, the direction used in the draft to show that kernels of quotient maps between strict LF-spaces of nuclear Fréchet spaces are again such spaces.
--
--   **Formalization Note** The step $P_m$ is the Lean quotient `X m ⧸ V.comap (X m).subtype` and $\iota_m$ is `Submodule.mapQ (V.comap (X m).subtype) V (X m).subtype le_rfl`; boundedness is von Neumann boundedness. The limit-subspace condition is written exactly as in `MasulloGRH.limit_subspace_iff_bounded_lifting`.
-- source:
--   A. M. Masullo, The Music of the Primes, draft of 20 November 2026, https://math216.wordpress.com/wp-content/uploads/2026/11/the-music-of-the-primes.pdf, Appendix C, Theorem C.1.5.11 (pp. 667-668) and the proof of Corollary C.1.5.13 (pp. 668-669); J. Wengenroth, Acyclic inductive spectra of Fréchet spaces, Studia Math. 120 (1996), §3, Cor. 3.4, p. 254

import Definitions.Def_MasulloGRH_LocallyConvex

set_option autoImplicit false

namespace MasulloGRH

theorem limit_subspace_of_bounded_lifting (E : Type*) [AddCommGroup E] [Module ℂ E]
    [TopologicalSpace E] (X : ℕ → Submodule ℂ E) (hmono : Monotone X)
    (hexh : ∀ x : E, ∃ n, x ∈ X n) (hX : ∀ n, IsFrechet (X n) ∧ IsNuclear (X n))
    (htop : ‹TopologicalSpace E› =
      sInf {t | IsLocallyConvexTopology E t ∧ ∀ n, @Continuous (X n) E _ t Subtype.val})
    (V : Submodule ℂ E) (hV : IsClosed (V : Set E))
    (hlift : LiftsBoundedSets (V.mkQ : E → E ⧸ V)) :
    (instTopologicalSpaceSubtype : TopologicalSpace V) =
        sInf {t | IsLocallyConvexTopology V t ∧
          ∀ n, @Continuous ↥(V ⊓ X n) V _ t (Submodule.inclusion inf_le_left)} := by sorry

end MasulloGRH
