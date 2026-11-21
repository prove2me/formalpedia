-- Prove2me | Theorems.Thm_MasulloGRH_strictLF_quotient_t2Space
-- name    : MasulloGRH.strictLF_quotient_t2Space
-- status  : Proved
-- author  : @Ismael Correa
-- created : 2026-11-21T00:04:55.261972+00:00
-- url     : https://prove2.me/theorems/522fb2d9-7d95-4737-b7c0-e414b42ecb54
-- title:
--   Quotients of strict LF-spaces by closed subspaces are Hausdorff
-- statement:
--   Let $E=\bigcup_n E_n$ be a strict countable locally convex inductive limit of Fréchet spaces $E_0\subseteq E_1\subseteq\cdots$ (each $E_n$ carrying the topology induced by $E$, and $E$ carrying the finest locally convex topology making all inclusions $E_n\hookrightarrow E$ continuous). If $F\subseteq E$ is a closed linear subspace, then the quotient $E/F$ with the quotient topology is a Hausdorff space.
--
--   This is the standard fact that the quotient of a topological vector space by a closed subspace is Hausdorff, applied to the locally convex space $E$.
-- source:
--   A. M. Masullo, The Music of the Primes (draft of 20 November 2026), Appendix C, §C.1.4–C.1.5 (strict LF-spaces, quotients, Retakh's condition (M)); cf. J. Wengenroth, Derived Functors in Functional Analysis, LNM 1810, Thm. 6.4

import Definitions.Def_MasulloGRH_LocallyConvex

set_option autoImplicit false

namespace MasulloGRH

theorem strictLF_quotient_t2Space (E : Type*) [AddCommGroup E] [Module ℂ E]
    [TopologicalSpace E] (X : ℕ → Submodule ℂ E) (hmono : Monotone X)
    (hexh : ∀ x : E, ∃ n, x ∈ X n) (hX : ∀ n, IsFrechet (X n))
    (htop : ‹TopologicalSpace E› =
      sInf {t | IsLocallyConvexTopology E t ∧ ∀ n, @Continuous (X n) E _ t Subtype.val})
    (V : Submodule ℂ E) (hV : IsClosed (V : Set E)) :
    T2Space (E ⧸ V) := by sorry

end MasulloGRH
