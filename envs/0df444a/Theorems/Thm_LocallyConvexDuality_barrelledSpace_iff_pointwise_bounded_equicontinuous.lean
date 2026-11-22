-- Prove2me | Theorems.Thm_LocallyConvexDuality_barrelledSpace_iff_pointwise_bounded_equicontinuous
-- name    : LocallyConvexDuality.barrelledSpace_iff_pointwise_bounded_equicontinuous
-- status  : Proved
-- author  : @emmgaml
-- created : 2026-11-22T09:21:01.918844+00:00
-- url     : https://prove2.me/theorems/2f441689-ff7f-452d-9a5e-ae9f121bb17c
-- title:
--   A locally convex space is barrelled iff every $\sigma(E',E)$-bounded subset of its dual $E'$ is equicontinuous
-- statement:
--   **Barrelled spaces are characterised by the uniform boundedness principle for functionals.**
--
--   Let $\mathbb K$ be $\mathbb R$ or $\mathbb C$, let $E$ be a locally convex topological $\mathbb K$-vector space and let $E'$ be its continuous dual. A subset $H\subset E'$ is $\sigma(E',E)$-bounded if and only if it is pointwise bounded, i.e. $\sup_{f\in H}|f(x)|<\infty$ for every $x\in E$; it is equicontinuous if there is a neighbourhood $U$ of $0$ in $E$ with $|f(x)|\le 1$ for all $f\in H$, $x\in U$. The following are equivalent:
--
--   1. $E$ is barrelled (every barrel of $E$, i.e. every closed, convex, circled, absorbing subset, is a neighbourhood of $0$);
--   2. every $\sigma(E',E)$-bounded subset of $E'$ is equicontinuous:
--   $$\Bigl(\forall x\in E:\ \sup_{f\in H}|f(x)|<\infty\Bigr)\ \Longrightarrow\ H\ \text{equicontinuous}\qquad\text{for all }H\subset E'.$$
--
--   The implication $1\Rightarrow 2$ is the Banach–Steinhaus theorem (uniform boundedness principle) for functionals, and $2\Rightarrow 1$ is its converse. This is the precise form of the "tighter relation between equicontinuous and bounded subsets" which the paper attributes to barrelled spaces at the end of §C.2.2.2.
--
--   **Deviation from the source.** The paper writes at this place that "the condition under which the strong-dual topology $\beta(E',E)$ agrees with the Mackey topology $\tau(E',E)$ is barreledness of $E$". That sentence is not correct as it stands (for the Banach space $E=c_0$, which is barrelled, $\beta(\ell^1,c_0)$ is the norm topology of $\ell^1$ with dual $\ell^\infty$, while $\tau(\ell^1,c_0)$ has dual $c_0$; equality of $\beta(E',E)$ and $\tau(E',E)$ characterises semi-reflexivity). The correct classical statement, formalized here, is that barrelledness of $E$ is equivalent to the equicontinuity of all weakly-$*$ bounded subsets of $E'$.
--
--   **Formalization Note.** `[RCLike 𝕜]`; "locally convex" is `PolynormableSpace 𝕜 E` (no Hausdorff hypothesis is needed), "barrelled" is Mathlib's `BarrelledSpace 𝕜 E` (every lower semicontinuous seminorm is continuous, equivalent to condition 1). The dual is `StrongDual 𝕜 E = E →L[𝕜] 𝕜`, used here only as a set of functionals (its topology plays no role); pointwise boundedness is `Bornology.IsBounded` of `{f x | f ∈ H}` in `𝕜`, and equicontinuity is Mathlib's `Equicontinuous` for the family indexed by the subtype `H`.
-- source:
--   A. M. Masullo, The Music of the Primes, draft of 20 November 2026, https://math216.wordpress.com/wp-content/uploads/2026/11/the-music-of-the-primes.pdf, pp. 674-675, §C.2.2.2 (unnumbered discussion of barrelled spaces, in corrected form: see the deviation recorded in the statement); the paper refers at this place to H. H. Schaefer, with M. P. Wolff, Topological Vector Spaces, Second Edition, Springer, Ch. II, §7 and Ch. III, 4.2-4.3

import Mathlib

set_option autoImplicit false

namespace LocallyConvexDuality

/-- A locally convex space `E` is barrelled iff every pointwise bounded (i.e. `σ(E', E)`-bounded)
set of continuous linear functionals on `E` is equicontinuous. -/
theorem barrelledSpace_iff_pointwise_bounded_equicontinuous {𝕜 E : Type*} [RCLike 𝕜]
    [AddCommGroup E] [Module 𝕜 E] [TopologicalSpace E] [IsTopologicalAddGroup E]
    [ContinuousSMul 𝕜 E] [PolynormableSpace 𝕜 E] :
    BarrelledSpace 𝕜 E ↔
      ∀ H : Set (StrongDual 𝕜 E),
        (∀ x : E, Bornology.IsBounded ((fun f : StrongDual 𝕜 E => f x) '' H)) →
          Equicontinuous (fun f : H => ((f : StrongDual 𝕜 E) : E → 𝕜)) := by sorry

end LocallyConvexDuality
