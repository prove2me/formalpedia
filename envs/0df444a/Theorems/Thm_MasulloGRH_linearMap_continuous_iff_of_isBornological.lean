-- Prove2me | Theorems.Thm_MasulloGRH_linearMap_continuous_iff_of_isBornological
-- name    : MasulloGRH.linearMap_continuous_iff_of_isBornological
-- status  : Proved
-- author  : @emmgaml
-- created : 2026-11-22T19:43:06.679449+00:00
-- url     : https://prove2.me/theorems/c6d80691-3b20-4e11-ad44-2f6585eaa9a8
-- title:
--   Linear maps out of a bornological space: continuous $\iff$ sequentially continuous $\iff$ bounded
-- statement:
--   **Continuity criterion for linear maps on a bornological space.**
--
--   Let $E$ and $F$ be locally convex topological vector spaces over $\mathbb C$ (topologies defined by families of seminorms), and assume that $E$ is *bornological*: every seminorm on $E$ that is bounded on each (von Neumann) bounded subset of $E$ is continuous. Let $T:E\to F$ be a $\mathbb C$-linear map. Then the following are equivalent:
--
--   1. $T$ is continuous;
--   2. $T$ is sequentially continuous: $x_n\to x$ in $E$ implies $Tx_n\to Tx$ in $F$;
--   3. $T$ is bounded: $T(B)$ is a bounded subset of $F$ for every bounded subset $B\subset E$.
--
--   Thus on bornological spaces (in particular on metrizable locally convex spaces and on LF-spaces) continuity of linear operators can be tested on convergent sequences or on bounded sets. In the proof of Proposition 2.4.3.1(2) (p. 114) the paper shows by dominated convergence that a linear operator on the Schwartz–Bruhat space $\mathcal S(\mathbf A_{F,S})$ with values in $L^1(J_{F,S},\bar\mu_S)$ is sequentially continuous, and concludes that it is continuous, citing [NB, Thm. 14.7.3] together with the facts that the strict LF-space $\mathcal S(\mathbf A_{F,S})$ is bornological and ultrabornological. The criterion above, combined with the bornologicity of strict LF-spaces, yields this conclusion directly.
--
--   **Formalization Note.** "Locally convex" is the platform predicate `MasulloGRH.IsLocallyConvexTopology` (the topology is given by some family of seminorms; no Hausdorff assumption is needed for this result) and "bornological" is the platform predicate `MasulloGRH.IsBornological` (every seminorm bounded on the von Neumann bounded sets is continuous), both from the definition file `Def_MasulloGRH_LocallyConvex`. Bounded sets are Mathlib's `Bornology.IsVonNBounded ℂ`, sequential continuity is `SeqContinuous`. The three equivalent conditions are stated as the two equivalences (1)$\Leftrightarrow$(2) and (1)$\Leftrightarrow$(3).
-- source:
--   A. M. Masullo, The Music of the Primes, draft of 20 November 2026, https://math216.wordpress.com/wp-content/uploads/2026/11/the-music-of-the-primes.pdf, p. 114, proof of Proposition 2.4.3.1(2)

import Mathlib
import Definitions.Def_MasulloGRH_LocallyConvex

set_option autoImplicit false

namespace MasulloGRH

/-- A linear map `T` from a bornological locally convex space `E` into a locally convex space `F`
(over `ℂ`) is continuous if and only if it is sequentially continuous, if and only if it maps
(von Neumann) bounded subsets of `E` to bounded subsets of `F`. -/
theorem linearMap_continuous_iff_of_isBornological (E F : Type*)
    [AddCommGroup E] [Module ℂ E] [TopologicalSpace E]
    [AddCommGroup F] [Module ℂ F] [TopologicalSpace F]
    (hE : IsLocallyConvexTopology E ‹TopologicalSpace E›) (hEb : IsBornological E)
    (hF : IsLocallyConvexTopology F ‹TopologicalSpace F›) (T : E →ₗ[ℂ] F) :
    (Continuous T ↔ SeqContinuous T) ∧
      (Continuous T ↔ ∀ B : Set E, Bornology.IsVonNBounded ℂ B →
        Bornology.IsVonNBounded ℂ (T '' B)) := by sorry

end MasulloGRH
