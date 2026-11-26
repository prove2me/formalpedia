-- Prove2me | Theorems.Thm_HurewiczSketchV2_low_skeleton_weakly_contractible
-- name    : HurewiczSketchV2.low_skeleton_weakly_contractible
-- status  : Open
-- author  : @loader3229
-- created : 2026-11-26T09:51:42.493073+00:00
-- url     : https://prove2.me/theorems/d4fcf894-c45e-416f-b6de-676bb5035a3d
-- title:
--   Low skeleton of a reduced CW model is weakly contractible and carries low homology
-- statement:
--   The low skeleton of a reduced CW model is weakly contractible and carries its low homology.
--
--   Let $Y$ be a reduced CW complex in degree $r=n+2$: $Y$ admits a CW structure and $\pi_k(Y,y)=0$ for all $k<r$ and all base points $y$.  Let $A$ be the $(n+1)$-skeleton of $Y$.  Then
--
--   * $A$ is a CW complex (a subcomplex of $Y$), and $A$ is $T_2$;
--   * $A$ is weakly contractible: for $k\le n+1$ cellular approximation identifies $\pi_k(A,a)$ with $\pi_k(Y,a)=0$, and for $k>n+1$ the homotopy groups vanish for dimensional reasons $\dim A\le n+1$;
--   * the relative cellular chain complex $C_\ast(Y,A)$ has no generators in degrees $<n+2$, so the long exact sequence of the pair gives: for $0<i<r$, $H_i(A;\mathbb{Z})=0$ implies $H_i(Y;\mathbb{Z})=0$ (an isomorphism for $i<r-1$, an epimorphism for $i=r-1$).
--
--   This is the cellular-chain computation that is the heart of step 2 of the Hurewicz proof.  Degree $i=0$ is deliberately excluded: $H_0$ of a nonempty space is $\mathbb{Z}$, not zero.
--
--   **Formalization Note** $A$ is bundled as a `TopCat` object; `T2Space A` and `Nonempty (CWComplex (Set.univ : Set A))` are recorded explicitly because Whitehead's theorem on the platform needs them.  Weak contractibility uses `SP4WeakHomotopy.WeaklyContractible`.  The homology transfer is stated as an implication `IsZero (H i A) → IsZero (H i Y)` to avoid committing to a particular relative-homology API, which Mathlib does not provide for CW pairs.
-- source:
--   A. Hatcher, Algebraic Topology, Cambridge University Press (2002), §4.1 Theorem 4.5 (Whitehead) p. 346 and Proposition 4.13 (cellular approximation) p. 353, §4.2 Theorem 4.32 (Hurewicz) p. 366; and https://zhuanlan.zhihu.com/p/2063085365225863035 (the three-step proof sketch followed here).

import Mathlib.Topology.Homotopy.HomotopyGroup
import Mathlib.Topology.Category.TopCat.Basic
import Mathlib.Topology.CWComplex.Classical.Basic
import Mathlib.Topology.Homotopy.Contractible
import Definitions.Def_HurewiczSketchV2
import Definitions.Def_SP4Homology
import Definitions.Def_SP4WeakHomotopy

set_option autoImplicit false

namespace HurewiczSketchV2

/-- The low skeleton of a reduced CW model is weakly contractible and carries its low homology.

Let `Y` be a reduced CW model in degree `r = n+2`: `Y` is a CW complex and
`π_k(Y,y)=0` for every `k<r` and every base point `y`.  Take the `(n+1)`-skeleton
`A` of `Y`.  It is a CW complex, and:

* in degrees `k ≤ n+1`, cellular approximation identifies `π_k(A,a)` with `π_k(Y,a)`,
  so it vanishes by the reduced-model hypothesis;
* in degrees `k > n+1`, `π_k(A,a)` vanishes because `dim A ≤ n+1`.

Hence `A` is weakly contractible.  Moreover the relative cellular chain complex
`C_*(Y,A)` starts in degree `n+2`, so for every `0<i<r` the map `H_i(A) → H_i(Y)`
is an isomorphism (`i<r-1`) or at least an epimorphism (`i=r-1`); in particular
`H_i(A)=0` forces `H_i(Y)=0`.  This transfer is the cellular-chain computation
that is the heart of step 2 of the Hurewicz proof. -/
theorem low_skeleton_weakly_contractible (n : ℕ) (Y : TopCat)
    (hY : ReducedCWModel (n + 2) Y) :
    ∃ (A : TopCat) (a : A),
      T2Space A ∧
      Nonempty (Topology.CWComplex (Set.univ : Set A)) ∧
      SP4WeakHomotopy.WeaklyContractible A ∧
      (∀ i : ℕ, 0 < i → i < n + 2 →
        CategoryTheory.Limits.IsZero (SP4Homology.H i A) →
          CategoryTheory.Limits.IsZero (SP4Homology.H i Y)) := by
  sorry

end HurewiczSketchV2
