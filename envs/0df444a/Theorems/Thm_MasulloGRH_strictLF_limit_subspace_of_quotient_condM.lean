-- Prove2me | Theorems.Thm_MasulloGRH_strictLF_limit_subspace_of_quotient_condM
-- name    : MasulloGRH.strictLF_limit_subspace_of_quotient_condM
-- status  : Proved
-- author  : @Ismael Correa
-- created : 2026-11-21T00:01:32.378366+00:00
-- url     : https://prove2.me/theorems/7eb19d0e-9ea2-450b-a0a4-aba39aa47d9b
-- title:
--   Condition (M) for the quotient spectrum makes a closed subspace a limit subspace
-- statement:
--   Let $E=\bigcup_m E_m$ be a strict countable locally convex inductive limit of nuclear Fréchet spaces $E_0\subseteq E_1\subseteq\cdots$ (each $E_m$ carries the topology induced by $E$, and $E$ carries the finest locally convex topology making all inclusions $E_m\hookrightarrow E$ continuous). Let $F\subseteq E$ be a closed linear subspace, $q\colon E\to E/F$ the quotient map, and $P_m=E_m/(F\cap E_m)$ with the quotient topology of $E_m$, with the natural continuous linear injections $\iota_m\colon P_m\to E/F$.
--
--   Assume that the quotient spectrum $(P_m)$ satisfies **Retakh's condition (M) for the quotient spectrum $(P_m)$**, written in terms of the steps $E_m$:
--
--   $$\forall n\ \exists m\ge n\ \exists U\in\mathcal U_0(E_n)\ \forall k\ge m\ \forall W\in\mathcal U_0(E_m)\ \exists W'\in\mathcal U_0(E_k):\quad q(U)\cap q(W')\subseteq q(W).$$
--
--   Then $F$ is a **limit subspace** of $E$: the topology induced on $F$ by $E$ coincides with the finest locally convex topology on $F$ for which all inclusions $F\cap E_m\hookrightarrow F$ are continuous.
--
--   This is Retakh's characterization of limit subspaces of strict LF-spaces (the sufficiency half): condition (M) for the quotient spectrum is equivalent to acyclicity of the quotient spectrum, which makes the short exact sequence of spectra $0\to(F\cap E_m)\to(E_m)\to(P_m)\to0$ topologically exact on the limit, i.e. $\operatorname{ind}(F\cap E_m)\to E$ is a topological embedding. It is the converse of `MasulloGRH.strictLF_quotient_condM_of_limit_subspace`.
--
--   **Formalization note.** Condition (M) is written exactly as in `MasulloGRH.strictLF_quotient_regular_of_condM` ($q(x)\in q(W')$ for $x\in U$ is written as $x-y\in F$ for some $y\in W'$); the regularity hypothesis exactly as in `MasulloGRH.strictLF_subspace_bornological_of_quotient_regular`; the limit-subspace condition exactly as in `MasulloGRH.limit_subspace_of_bounded_lifting`.
-- source:
--   A. M. Masullo, The Music of the Primes, draft of 20 November 2026, https://math216.wordpress.com/wp-content/uploads/2026/11/the-music-of-the-primes.pdf, Appendix C, Theorem C.1.5.11 (pp. 667-668); J. Wengenroth, Acyclic inductive spectra of Fréchet spaces, Studia Math. 120 (1996), §3, Cor. 3.4, p. 254; V. S. Retakh, Subspaces of a countable inductive limit, Soviet Math. Dokl. 11 (1970), 1384-1386

import Definitions.Def_MasulloGRH_LocallyConvex

set_option autoImplicit false

namespace MasulloGRH

theorem strictLF_limit_subspace_of_quotient_condM
    (E : Type*) [AddCommGroup E] [Module ℂ E]
    [TopologicalSpace E] (X : ℕ → Submodule ℂ E) (hmono : Monotone X)
    (hexh : ∀ x : E, ∃ n, x ∈ X n) (hX : ∀ n, IsFrechet (X n) ∧ IsNuclear (X n))
    (htop : ‹TopologicalSpace E› =
      sInf {t | IsLocallyConvexTopology E t ∧ ∀ n, @Continuous (X n) E _ t Subtype.val})
    (V : Submodule ℂ E) (hV : IsClosed (V : Set E))
    (hM : ∀ n : ℕ, ∃ m : ℕ, n ≤ m ∧ ∃ U ∈ nhds (0 : X n), ∀ k : ℕ, m ≤ k →
      ∀ W ∈ nhds (0 : X m), ∃ W' ∈ nhds (0 : X k),
        ∀ x ∈ U, ∀ y ∈ W', ((x : E) - (y : E)) ∈ V → ∃ w ∈ W, ((x : E) - (w : E)) ∈ V) :
    (instTopologicalSpaceSubtype : TopologicalSpace V) =
        sInf {t | IsLocallyConvexTopology V t ∧
          ∀ n, @Continuous ↥(V ⊓ X n) V _ t (Submodule.inclusion inf_le_left)} := by sorry

end MasulloGRH
