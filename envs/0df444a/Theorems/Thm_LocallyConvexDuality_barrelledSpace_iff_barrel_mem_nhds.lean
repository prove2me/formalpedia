-- Prove2me | Theorems.Thm_LocallyConvexDuality_barrelledSpace_iff_barrel_mem_nhds
-- name    : LocallyConvexDuality.barrelledSpace_iff_barrel_mem_nhds
-- status  : Proved
-- author  : @emmgaml
-- created : 2026-11-22T09:21:03.985802+00:00
-- url     : https://prove2.me/theorems/efedfc87-dfff-4a6b-abff-873c7c439baa
-- title:
--   A topological vector space is barrelled (lower semicontinuous seminorms are continuous) iff every barrel is a neighbourhood of $0$
-- statement:
--   **Barrelled spaces: the seminorm definition agrees with the definition by barrels.**
--
--   Let $\mathbb K$ be $\mathbb R$ or $\mathbb C$ and let $E$ be a topological $\mathbb K$-vector space. A *barrel* in $E$ is a subset $D\subset E$ which is closed, convex, circled (balanced: $\lambda D\subset D$ for $|\lambda|\le 1$) and absorbing (every $x\in E$ lies in $\lambda D$ for all scalars $\lambda$ with $|\lambda|$ large enough). The following are equivalent:
--
--   1. every lower semicontinuous seminorm on $E$ is continuous (this is the definition of a barrelled space used by Mathlib);
--   2. every barrel of $E$ is a neighbourhood of $0$ (the classical definition of a barrelled space, recalled in the paper for locally convex spaces).
--
--   The equivalence identifies Mathlib's notion `BarrelledSpace` with the textbook notion used throughout the paper (Fréchet spaces and strict LF-spaces are barrelled; hypotheses of the Banach–Steinhaus theorem and of Lemma C.2.1.7).
--
--   **Formalization Note.** `[RCLike 𝕜]`, and `E` is any topological vector space over `𝕜` (`IsTopologicalAddGroup`, `ContinuousSMul`); the paper and the classical literature consider barrelled spaces only among (Hausdorff) locally convex spaces, but the equivalence between the two formulations holds, with the same statement, for every topological vector space, and it is stated in this generality. "Convex and circled" is `AbsConvex 𝕜 D` (balanced, and convex for the `ComplexOrder` order on `𝕜`, i.e. for real convex combinations) and "absorbing" is `Absorbent 𝕜 D`.
-- source:
--   A. M. Masullo, The Music of the Primes, draft of 20 November 2026, https://math216.wordpress.com/wp-content/uploads/2026/11/the-music-of-the-primes.pdf, pp. 674-675, §C.2.2.2 (unnumbered: definition of barrelled spaces by barrels); classical reference: H. H. Schaefer, with M. P. Wolff, Topological Vector Spaces, Second Edition, Springer, Ch. II, §7 (as cited by the paper)

import Mathlib

open scoped Topology ComplexOrder

set_option autoImplicit false

namespace LocallyConvexDuality

/-- Mathlib's `BarrelledSpace` (every lower semicontinuous seminorm is continuous) is equivalent to
the classical definition: every barrel (closed, convex, circled, absorbing set) is a neighbourhood
of `0`. -/
theorem barrelledSpace_iff_barrel_mem_nhds {𝕜 E : Type*} [RCLike 𝕜] [AddCommGroup E] [Module 𝕜 E]
    [TopologicalSpace E] [IsTopologicalAddGroup E] [ContinuousSMul 𝕜 E] :
    BarrelledSpace 𝕜 E ↔
      ∀ D : Set E, IsClosed D → AbsConvex 𝕜 D → Absorbent 𝕜 D → D ∈ 𝓝 (0 : E) := by sorry

end LocallyConvexDuality
