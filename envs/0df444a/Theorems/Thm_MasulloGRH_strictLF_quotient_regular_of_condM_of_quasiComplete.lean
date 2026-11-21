-- Prove2me | Theorems.Thm_MasulloGRH_strictLF_quotient_regular_of_condM_of_quasiComplete
-- name    : MasulloGRH.strictLF_quotient_regular_of_condM_of_quasiComplete
-- status  : Proved
-- author  : @Ismael Correa
-- created : 2026-11-20T23:56:02.382174+00:00
-- url     : https://prove2.me/theorems/92e6a558-26f6-4e03-af13-7097cf30253b
-- title:
--   Quasi-complete quotients of strict LF-spaces are regular (Grothendieck factorization)
-- statement:
--   Let $E=\bigcup_n E_n$ be a strict countable locally convex inductive limit of nuclear Fréchet spaces $E_0\subseteq E_1\subseteq\cdots$ (each $E_n$ with the topology induced by $E$; $E$ with the finest locally convex topology making all inclusions continuous). Let $F\subseteq E$ be a closed linear subspace, $q\colon E\to E/F$ the quotient map (with the quotient topology) and $P_n=E_n/(F\cap E_n)$ the quotient steps, with natural continuous injections $\iota_n\colon P_n\to E/F$. Here $\mathcal U_0(\cdot)$ denotes the filter of $0$-neighbourhoods.
--
--   Assume that the quotient $E/F$ is quasi-complete (Hausdorff, and every bounded Cauchy filter converges). Then $E/F$ is regular with respect to the steps $P_m$:
--   $$\forall B\subseteq E/F\ \text{bounded}\quad\exists m,\ \exists A\subseteq P_m\ \text{bounded}:\quad B\subseteq\iota_m(A).$$
--
--   Boundedness is von Neumann boundedness. This is the classical consequence of Grothendieck's factorization theorem: in a quasi-complete space the closed absolutely convex hull of a bounded set is a Banach disk, and a continuous linear map from a Banach space into the LF-space $E/F=\operatorname{ind}P_m$ factors continuously through one of the Fréchet steps $P_m$.
-- source:
--   A. Grothendieck's factorization theorem, see H. Jarchow, Locally Convex Spaces (1981), Theorem 5.6.3 / K. Floret, Some aspects of the theory of locally convex inductive limits (1980), and J. Wengenroth, Derived Functors in Functional Analysis, LNM 1810 (2003), Section 6.1; used in A. M. Masullo, The Music of the Primes, draft of 20 November 2026, Appendix C, Theorem C.1.5.11 (pp. 667-669)

import Definitions.Def_MasulloGRH_LocallyConvex

set_option autoImplicit false

namespace MasulloGRH

theorem strictLF_quotient_regular_of_condM_of_quasiComplete (E : Type*) [AddCommGroup E] [Module ℂ E]
    [TopologicalSpace E] (X : ℕ → Submodule ℂ E) (hmono : Monotone X)
    (hexh : ∀ x : E, ∃ n, x ∈ X n) (hX : ∀ n, IsFrechet (X n) ∧ IsNuclear (X n))
    (htop : ‹TopologicalSpace E› =
      sInf {t | IsLocallyConvexTopology E t ∧ ∀ n, @Continuous (X n) E _ t Subtype.val})
    (V : Submodule ℂ E) (hV : IsClosed (V : Set E))
    (hQ : IsQuasiComplete (E ⧸ V)) :
    ∀ B : Set (E ⧸ V), Bornology.IsVonNBounded ℂ B →
      ∃ (n : ℕ) (A : Set (X n ⧸ V.comap (X n).subtype)), Bornology.IsVonNBounded ℂ A ∧
        B ⊆ Submodule.mapQ (V.comap (X n).subtype) V (X n).subtype le_rfl '' A := by sorry

end MasulloGRH
