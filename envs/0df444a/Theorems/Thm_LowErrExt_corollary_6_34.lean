-- Prove2me | Theorems.Thm_LowErrExt_corollary_6_34
-- name    : LowErrExt.corollary_6_34
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T16:54:27.341746+00:00
-- url     : https://prove2.me/theorems/78c75531-fffa-4292-ab71-2a8a04abef25
-- title:
--   Corollary 6.34 — spreadness implies rapid mixing
-- statement:
--   Let $m\ge2$. There are constants $C,C'\ge1$ depending only on $m$ such that the following holds. Let $G$ be a finite abelian group with torsion $m$, $V\subseteq G$ a coset with $n:=H_0[V]$, and $\mathbf X$ a source that is $(r,k)_2$-spread in $V$ with $n\ge k\ge C$. Then for some integer $0\le t\le C'\log(n/k)$,
--   $$H_2\big[2^{t-1}\mathbf X-2^{t-1}\mathbf X\big]\ge n-r .$$
--
--   A spread source mixes to entropy gap $r$ within $O(\log(n/k))$ differencing steps; this is the paper's main engine.
--
--   Differences from the source:
--   - encoding: G has torsion m → m • x = 0 for every x ∈ G; reason: the paper's meaning of bounded torsion (footnote 20, p.40); same instances
--   - encoding: spreadness over all homomorphisms L out of G (Definition 6.2) → spreadness over the quotient maps G → G/K for subgroups K (IsSpread); reason: a homomorphism with kernel K is an injective map after π_K, so images and entropies agree (Observation 6.5's argument); same instances
-- source:
--   D. Doron, J. Goodman, Low-Error Extractors, STOC 2027 submission (manuscript sha256 43c922d6…), Corollary 6.34, p.50 (= Theorem 7.13, p.54)

import Mathlib
import Definitions.Def_LowErrExt_H2
import Definitions.Def_LowErrExt_iterDiff
import Definitions.Def_LowErrExt_IsCoset
import Definitions.Def_LowErrExt_IsSpread

namespace LowErrExt

/-- **Corollary 6.34 (Spreadness implies rapid mixing).**
Doron, Goodman, *Low-Error Extractors*, STOC 2027 submission (manuscript sha256 43c922d6…),
Corollary 6.34, p.50 (restated as Theorem 7.13, p.54): "Let G be a finite abelian group with torsion
m ≥ 2, and let V ⊆ G be a coset with n := H0[V]. There are constants C, C′ ≥ 1 depending only on m
such that the following holds. If X ∼ V is (r, k)2-spread in V, and n ≥ k ≥ C, then
H2[2^{t−1}X − 2^{t−1}X] ≥ n − r for some t ≤ C′ log(n/k)."

**Formalization Note.** `t ∈ ℕ`, `t = 0` meaning `X` itself (footnote 24, p.50); log base 2. -/
theorem corollary_6_34 (m : ℕ) (hm : 2 ≤ m) :
    ∃ C C' : ℝ, 1 ≤ C ∧ 1 ≤ C' ∧
      ∀ (G : Type) [AddCommGroup G] [Fintype G], (∀ x : G, m • x = 0) →
        ∀ (V : Set G) (X : PMF G) (r k : ℝ), IsCoset V → IsSpread2 r k V X →
          k ≤ H0 V → C ≤ k →
            ∃ t : ℕ, (t : ℝ) ≤ C' * Real.logb 2 (H0 V / k) ∧
              H0 V - r ≤ H2 (iterDiff t X) := by sorry

end LowErrExt
