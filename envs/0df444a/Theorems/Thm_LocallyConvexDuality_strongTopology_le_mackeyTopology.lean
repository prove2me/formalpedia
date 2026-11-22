-- Prove2me | Theorems.Thm_LocallyConvexDuality_strongTopology_le_mackeyTopology
-- name    : LocallyConvexDuality.strongTopology_le_mackeyTopology
-- status  : Proved
-- author  : @emmgaml
-- created : 2026-11-22T09:22:46.983602+00:00
-- url     : https://prove2.me/theorems/eced238b-89c7-4c20-8f8e-9996048dfd10
-- title:
--   The strong topology $\beta(E,F)$ of a pairing is finer than the Mackey topology $\tau(E,F)$
-- statement:
--   **The strong topology of a pairing is finer than its Mackey topology.**
--
--   Let $\mathbb K$ be $\mathbb R$ or $\mathbb C$, let $E,F$ be $\mathbb K$-vector spaces and let $\langle\cdot,\cdot\rangle:E\times F\to\mathbb K$ be a bilinear pairing. On $E$ consider
--
--   * the Mackey topology $\tau(E,F)$: uniform convergence on all convex, circled, $\sigma(F,E)$-compact subsets of $F$;
--   * the strong topology $\beta(E,F)$: uniform convergence on all $\sigma(F,E)$-bounded subsets of $F$.
--
--   Then $\beta(E,F)$ is finer than (or equal to) $\tau(E,F)$:
--   $$\tau(E,F)\ \subseteq\ \beta(E,F)\qquad\text{(every }\tau(E,F)\text{-open set is }\beta(E,F)\text{-open).}$$
--
--   The paper records this on p. 674 ("the strong topology $\beta(E,F)$ ... is always stronger than the Mackey topology"). Together with the Mackey–Arens theorem it shows that, for a dual pair, $\beta(E,F)$ is compatible with the pairing exactly when it coincides with $\tau(E,F)$, which fails in general.
--
--   **Formalization Note.** `strongTopology` and `mackeyTopology` are the definitions from `LocallyConvexDuality_PolarTopology`, for a pairing `B : E →ₗ[𝕜] F →ₗ[𝕜] 𝕜` with `[RCLike 𝕜]`. In Mathlib's order on `TopologicalSpace E`, `t₁ ≤ t₂` means that `t₁` is finer than `t₂`, so the statement reads `strongTopology B ≤ mackeyTopology B`. The paper works with a separating pairing; the comparison holds for every bilinear pairing and no separation hypothesis is imposed.
-- source:
--   A. M. Masullo, The Music of the Primes, draft of 20 November 2026, https://math216.wordpress.com/wp-content/uploads/2026/11/the-music-of-the-primes.pdf, p. 674, §C.2.2.2 (unnumbered: 'the strong topology β(E,F) that is always stronger than the Mackey topology')

import Mathlib
import Definitions.Def_LocallyConvexDuality_PolarTopology

set_option autoImplicit false

namespace LocallyConvexDuality

/-- The strong topology `β(E, F)` is finer than the Mackey topology `τ(E, F)`
(in Mathlib's order on topologies, finer means `≤`). -/
theorem strongTopology_le_mackeyTopology {𝕜 E F : Type*} [RCLike 𝕜] [AddCommGroup E] [Module 𝕜 E]
    [AddCommGroup F] [Module 𝕜 F] (B : E →ₗ[𝕜] F →ₗ[𝕜] 𝕜) :
    strongTopology B ≤ mackeyTopology B := by sorry

end LocallyConvexDuality
