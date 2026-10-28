-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff12_coarse_failure_reduction
-- name    : HlawkaSchatten.DiagonalCutoff12.coarse_failure_reduction
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-27T01:39:38.288963+00:00
-- url     : https://prove2.me/theorems/26fc28fa-e46b-455a-9789-c989a397c78f
-- title:
--   Relative-coordinate reduction of a Hlawka counterexample for p >= 12
-- statement:
--   Let $p\ge12$, and let $K_p$ be the cyclic Hlawka constant. Suppose
--   $$\frac{1041}{2500}p<K_p,\qquad E_p\!\left(\frac{549}{1250}\right)<K_p,$$
--   where $E_p$ is the scalar total-norm envelope. If a real three-dimensional triple has negative Hlawka deficit with constant $K_p$, there is another such triple, written as the rows of $X$, satisfying
--   $$\sum_i\|X_i\|_p=3,\qquad 1\le\|X_0+X_1+X_2\|_p\le\frac{1647}{1250},$$
--   and, for distinct $i,j,k$,
--   $$\|X_j+X_k\|_p\le X_{ji}+X_{ki}+\frac1{2000}.$$
--   Thus each pair norm is approximated from above by its assigned principal coordinate with a uniform additive error. This is a counterexample-reduction lemma; the scalar hypotheses and exclusion of the resulting localized triples are separate steps.
-- source:
--   Cutoff-12 improvement in the sharp diagonal Hlawka campaign: https://prove2.me/theorems/7fe6f02d-65e5-4c21-9796-c83889b29b9d . Uses the previously proved normalization, weighted-pair envelope, and envelope-monotonicity theorems. Generic arguments retain the Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_DiagonalConstruction_Basic
import Definitions.Def_HlawkaSchatten_DiagonalConstruction_Cyclic
import Definitions.Def_HlawkaSchatten_DiagonalConstruction_ScalarBounds
import Definitions.Def_HlawkaSchatten_DiagonalConstruction_Localization
open HlawkaSchatten HlawkaSchatten.DiagonalConstruction

theorem HlawkaSchatten.DiagonalCutoff12.coarse_failure_reduction
    {p : ℝ} (hp : 12 ≤ p)
    (hlinear : (1041/2500 : ℝ)*p < cyclicConstant p)
    (henvelope : scalarEnvelope p (549/1250) < cyclicConstant p)
    (x y z : Fin 3 → ℝ) (hf : hlawkaDeficit p (cyclicConstant p) x y z < 0) :
    ∃ X : Fin 3 → Fin 3 → ℝ,
      lpNorm p (X 0)+lpNorm p (X 1)+lpNorm p (X 2) = 3 ∧
      1 ≤ lpNorm p (X 0+X 1+X 2) ∧
      lpNorm p (X 0+X 1+X 2) ≤ 1647/1250 ∧
      (∀ i j k : Fin 3, i ≠ j → i ≠ k → j ≠ k →
        lpNorm p (X j+X k) ≤ X j i+X k i+1/2000) ∧
      tripleDeficit p (cyclicConstant p) X < 0 := by sorry
