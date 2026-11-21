-- Prove2me | Theorems.Thm_MasulloGRH_strictLF_nhds_zero_of_absConvex_traces
-- name    : MasulloGRH.strictLF_nhds_zero_of_absConvex_traces
-- status  : Proved
-- author  : @Ismael Correa
-- created : 2026-11-21T00:08:15.911104+00:00
-- url     : https://prove2.me/theorems/c3fc33a4-440f-4f0c-9eb3-c50ef0f09f20
-- title:
--   Strict LF-spaces: an absolutely convex set with neighbourhood traces is a $0$-neighbourhood
-- statement:
--   Let $E=\bigcup_n X_n$ be a strict LF-space over $\mathbb C$: $(X_n)$ is an increasing exhausting sequence of subspaces, each Fréchet for the topology induced by $E$, and the topology of $E$ is the finest locally convex topology making all inclusions $X_n\hookrightarrow E$ continuous. If $\Omega\subseteq E$ is absolutely convex (convex and balanced) and $\Omega\cap X_n$ is a $0$-neighbourhood of $X_n$ for every $n$, then $\Omega$ is a $0$-neighbourhood of $E$.
--
--   This is the standard description of the $0$-neighbourhoods of a locally convex inductive limit: the gauge of $\Omega$ is a seminorm continuous on every step, hence it defines a locally convex topology for which all inclusions are continuous, and the inductive limit topology is finer than it.
-- source:
--   A. M. Masullo, The Music of the Primes (draft 20 Nov 2026), Appendix C, Example C.1.4.6(4), p. 664; cf. Köthe, Topological Vector Spaces I, §19.1; Schaefer, TVS, II.6.

import Definitions.Def_MasulloGRH_LocallyConvex

set_option autoImplicit false

namespace MasulloGRH

theorem strictLF_nhds_zero_of_absConvex_traces (E : Type*) [AddCommGroup E] [Module ℂ E]
    [TopologicalSpace E] (X : ℕ → Submodule ℂ E) (hmono : Monotone X)
    (hexh : ∀ x : E, ∃ n, x ∈ X n) (hX : ∀ n, IsFrechet (X n))
    (htop : ‹TopologicalSpace E› =
      sInf {t | IsLocallyConvexTopology E t ∧ ∀ n, @Continuous (X n) E _ t Subtype.val})
    (Ω : Set E) (hconv : Convex ℝ Ω) (hbal : Balanced ℂ Ω)
    (htr : ∀ n, ((↑) : X n → E) ⁻¹' Ω ∈ nhds (0 : X n)) :
    Ω ∈ nhds (0 : E) := by sorry

end MasulloGRH
