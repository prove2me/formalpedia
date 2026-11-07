-- Prove2me | Theorems.Thm_LowErrExt_theorem_6_25
-- name    : LowErrExt.theorem_6_25
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T16:54:27.953323+00:00
-- url     : https://prove2.me/theorems/7eaac141-fc54-4583-b7a0-2006126c2ff2
-- title:
--   Theorem 6.25 — spreadness PFR
-- statement:
--   Let $m\ge2$. There are constants $c,C>0$ depending only on $m$ such that the following holds. Let $G$ be a finite abelian group with torsion $m$, $V\subseteq G$ a coset, $\mathbf X$ a source supported in $V$, and $k\ge0$. If $\mathbf X$ is $(r,k)_2$-spread in $V$ and $(r-k,d)_2$-spread in $V$, then
--   $$\mathbf X-\mathbf X\ \text{ is }\ (r,\,k+cd-C)_2\text{-spread in } V-V .$$
--
--   Differencing a spread source increases its spreadness at the same resolution; it is the growth step behind Theorem 6.32.
--
--   Differences from the source:
--   - encoding: G has torsion m → m • x = 0 for every x ∈ G; reason: the paper's meaning of bounded torsion (footnote 20, p.40); same instances
--   - encoding: spreadness over all homomorphisms L out of G (Definition 6.2) → spreadness over the quotient maps G → G/K for subgroups K (IsSpread); reason: a homomorphism with kernel K is an injective map after π_K, so images and entropies agree (Observation 6.5's argument); same instances
-- source:
--   D. Doron, J. Goodman, Low-Error Extractors, STOC 2027 submission (manuscript sha256 43c922d6…), Theorem 6.25, p.44

import Mathlib
import Definitions.Def_LowErrExt_iterDiff
import Definitions.Def_LowErrExt_IsCoset
import Definitions.Def_LowErrExt_IsSpread

open Pointwise

namespace LowErrExt

/-- **Theorem 6.25 (Spreadness PFR).**
Doron, Goodman, *Low-Error Extractors*, STOC 2027 submission (manuscript sha256 43c922d6…),
Theorem 6.25, p.44: "Let G be a finite abelian group with torsion m ≥ 2, let V ⊆ G be a coset, let
X ∼ V be a random variable, and let k ≥ 0. If X is (r, k)2-spread in V and (r − k, d)2-spread in V,
then X − X is (r, k + cd − C)2-spread in V − V, where c, C > 0 are constants depending only on m."

**Formalization Note.** `X ∼ V` is part of `IsSpread2`. `V − V` is the pointwise difference set and
`X − X` the difference of two independent copies. `r`, `d` are arbitrary reals. -/
theorem theorem_6_25 (m : ℕ) (hm : 2 ≤ m) :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧
      ∀ (G : Type) [AddCommGroup G] [Fintype G], (∀ x : G, m • x = 0) →
        ∀ (V : Set G) (X : PMF G) (r k d : ℝ), IsCoset V → 0 ≤ k →
          IsSpread2 r k V X → IsSpread2 (r - k) d V X →
            IsSpread2 r (k + c * d - C) (V - V) (diffLaw X) := by sorry

end LowErrExt
