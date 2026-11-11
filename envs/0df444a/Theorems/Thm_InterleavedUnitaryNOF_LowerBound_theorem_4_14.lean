-- Prove2me | Theorems.Thm_InterleavedUnitaryNOF_LowerBound_theorem_4_14
-- name    : InterleavedUnitaryNOF.LowerBound.theorem_4_14
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T07:10:26.254955+00:00
-- url     : https://prove2.me/theorems/15a7b4bb-a0b2-484b-9bd9-c7f6e8a54488
-- title:
--   Theorem 4.14 — KLM relative deviation, constant 20
-- statement:
--   Consider a finite-type box $B_i=\mathcal X_i\times\mathcal Y_i\times\mathcal Z_i$ from equal-measure partitions, with nonzero local Boolean factors $f_i,g_i$. Let $0<\epsilon<1/20$, let $\ell\ge2$ be even, and suppose $\lceil\ell/\epsilon\rceil\le d$. If both factors are $(\epsilon,d)$-regular and satisfy $\epsilon$-min-degree on their local domains, then
--
--   $$\left\|\frac{\mathbb E_{Z\sim\mathcal Z_i}[f_i(Y,Z)g_i(X,Z)]}{\delta_{f,i}\delta_{g,i}}-1\right\|_\ell\le20\epsilon.$$
--
--   The densities and the norm use normalized local Haar measure; the norm is on $\mathcal X_i\times\mathcal Y_i$. Nonzero finite-type factors have strictly positive local densities.
--
--   Differences from the source:
--   - encoding: positive matrix dimension and measurable Boolean functions on SU(m) powers → Fin m with NeZero m, normalized Borel Haar on the actual matrix group, and Bool indicators valued in ℝ; reason: these represent exactly the source objects, including m=1, without a discretization of the group
--   - generalization: a fixed decomposition index i → any box on the same equal-measure partitions with the stated local hypotheses; reason: the relative-deviation result depends on the local functions and normalized domains, not the global decomposition
--   - encoding: nonzero finite-type Boolean factors and ceil(ℓ/ε)≤d → positive local densities and Nat.ceil of the positive ratio; reason: cell constancy and positive equal cell measures make nonzero equivalent to positive density; no denominator can vanish
-- source:
--   Haoyu Wang, Pei Wu, Guangxu Yang, STOC 2027 submission #1513 (October 2026), Theorem 4.14, printed p.17 = PDF p.17; https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1513.pdf

import Mathlib
import Definitions.Def_InterleavedUnitaryNOF_LowerBound_Regularity

open MeasureTheory

namespace InterleavedUnitaryNOF.LowerBound

theorem theorem_4_14 (m : ℕ) [NeZero m] (c : Cylinder m)
    (P : CylinderPartitions c) (B : BoxPiece m) (hP : RespectsPartitions P B)
    (ε : ℝ) (hε : 0 < ε) (hε' : ε < (1 : ℝ)/20)
    (ℓ d : ℕ) (hℓ : 2 ≤ ℓ) (heven : Even ℓ) (hd : Nat.ceil ((ℓ : ℝ)/ε) ≤ d)
    (hf : 0 < B.df) (hg : 0 < B.dg) (hreg : B.Pseudorandom ε d) :
    lpNorm (B.xLaw.prod B.yLaw)
      (fun xy => (∫ z, bval (B.f (xy.2,z))*bval (B.g (xy.1,z)) ∂B.zLaw) /
        (B.df*B.dg) - 1) ℓ ≤ 20*ε := by sorry

end InterleavedUnitaryNOF.LowerBound
