-- Prove2me | Theorems.Thm_MasulloGRH_strictLF_quotient_regular_of_limit_subspace
-- name    : MasulloGRH.strictLF_quotient_regular_of_limit_subspace
-- status  : Proved
-- author  : @Ismael Correa
-- created : 2026-11-20T23:20:53.157+00:00
-- url     : https://prove2.me/theorems/9a39605b-de2f-4cf1-8dbf-dd5792912ca9
-- title:
--   Limit subspaces of strict LF-spaces of nuclear Fréchet spaces have regular quotients
-- statement:
--   Let $E$ be a strict countable locally convex inductive limit of nuclear Fréchet spaces: $E=\bigcup_m E_m$ for an increasing sequence of subspaces $E_0\subseteq E_1\subseteq\cdots$, each a nuclear Fréchet space for the topology induced by $E$, and $E$ carries the finest locally convex topology for which all inclusions $E_m\hookrightarrow E$ are continuous. Let $F\subseteq E$ be a closed linear subspace, $q\colon E\to E/F$ the quotient map, and for each $m$ let $P_m=E_m/(F\cap E_m)$ with the quotient topology of $E_m$, together with the natural continuous linear injection $\iota_m\colon P_m\to E/F$.
--
--   Assume $F$ is a **limit subspace**: the topology induced on $F$ by $E$ equals the locally convex inductive limit topology of the subspaces $F\cap E_m$, each with the topology induced from $E$ (equivalently from $E_m$). Then the quotient is **regular with respect to the steps $P_m$**: every bounded subset $B\subseteq E/F$ is contained in $\iota_m(A)$ for some $m$ and some bounded subset $A\subseteq P_m$:
--
--   $$\forall B\subseteq E/F\ \text{bounded}\quad\exists m,\ \exists A\subseteq P_m\ \text{bounded}:\quad B\subseteq\iota_m(A).$$
--
--   This is one half of the homological content of Theorem C.1.5.11: when $F$ is itself the strict inductive limit of the $F\cap E_m$, the quotient inductive system $(P_m)$ inherits the good behaviour (acyclicity, hence regularity) of the strict system $(E_m)$.
--
--   **Formalization Note** The step $P_m$ is the Lean quotient `X m ⧸ V.comap (X m).subtype` and $\iota_m$ is `Submodule.mapQ (V.comap (X m).subtype) V (X m).subtype le_rfl`; boundedness is von Neumann boundedness. The limit-subspace condition is written exactly as in `MasulloGRH.limit_subspace_iff_bounded_lifting`.
-- source:
--   A. M. Masullo, The Music of the Primes, draft of 20 November 2026, https://math216.wordpress.com/wp-content/uploads/2026/11/the-music-of-the-primes.pdf, Appendix C, Theorem C.1.5.11 (pp. 667-668) and the proof of Corollary C.1.5.13 (pp. 668-669); J. Wengenroth, Acyclic inductive spectra of Fréchet spaces, Studia Math. 120 (1996), §3, Cor. 3.4, p. 254

import Definitions.Def_MasulloGRH_LocallyConvex

set_option autoImplicit false

namespace MasulloGRH

theorem strictLF_quotient_regular_of_limit_subspace (E : Type*) [AddCommGroup E] [Module ℂ E]
    [TopologicalSpace E] (X : ℕ → Submodule ℂ E) (hmono : Monotone X)
    (hexh : ∀ x : E, ∃ n, x ∈ X n) (hX : ∀ n, IsFrechet (X n) ∧ IsNuclear (X n))
    (htop : ‹TopologicalSpace E› =
      sInf {t | IsLocallyConvexTopology E t ∧ ∀ n, @Continuous (X n) E _ t Subtype.val})
    (V : Submodule ℂ E) (hV : IsClosed (V : Set E))
    (hlim : (instTopologicalSpaceSubtype : TopologicalSpace V) =
        sInf {t | IsLocallyConvexTopology V t ∧
          ∀ n, @Continuous ↥(V ⊓ X n) V _ t (Submodule.inclusion inf_le_left)}) :
    ∀ B : Set (E ⧸ V), Bornology.IsVonNBounded ℂ B →
      ∃ (n : ℕ) (A : Set (X n ⧸ V.comap (X n).subtype)), Bornology.IsVonNBounded ℂ A ∧
        B ⊆ Submodule.mapQ (V.comap (X n).subtype) V (X n).subtype le_rfl '' A := by sorry

end MasulloGRH
