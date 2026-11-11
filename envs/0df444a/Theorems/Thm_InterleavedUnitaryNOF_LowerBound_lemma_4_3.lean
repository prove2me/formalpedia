-- Prove2me | Theorems.Thm_InterleavedUnitaryNOF_LowerBound_lemma_4_3
-- name    : InterleavedUnitaryNOF.LowerBound.lemma_4_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T07:09:46.276784+00:00
-- url     : https://prove2.me/theorems/ee568da1-a3ee-4852-b163-820e8532cd6f
-- title:
--   Lemma 4.3 — corruption bound
-- statement:
--   For $m\ge1$, use the product Haar law $\mu_0$ and the constrained law $\mu_1$ on $SU(m)^4\times SU(m)^4\times SU(m)^2$. A measurable cylinder indicator has the form $c(X,Y,Z)=f(Y,Z)g(X,Z)h(X,Y)$ for measurable Boolean factors. There are universal constants $\alpha>1$ and $\beta>0$, chosen independently of the dimension and the factors, such that
--
--   $$\mu_1(c)\le\alpha\mu_0(c)+\exp(-\beta m^{1/16}).$$
--
--   This comparison applies to every measurable cylinder, without a finite-type hypothesis.
--
--   Differences from the source:
--   - encoding: positive matrix dimension and measurable Boolean functions on SU(m) powers → Fin m with NeZero m, normalized Borel Haar on the actual matrix group, and Bool indicators valued in ℝ; reason: these represent exactly the source objects, including m=1, without a discretization of the group
-- source:
--   Haoyu Wang, Pei Wu, Guangxu Yang, STOC 2027 submission #1513 (October 2026), Lemma 4.3, printed p.10 = PDF p.10; https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1513.pdf

import Mathlib
import Definitions.Def_InterleavedUnitaryNOF_LowerBound_Regularity

open MeasureTheory

namespace InterleavedUnitaryNOF.LowerBound

theorem lemma_4_3 : ∃ α β : ℝ, 1 < α ∧ 0 < β ∧
    ∀ (m : ℕ) [NeZero m] (c : Cylinder m),
      mass (mu1 m) c ≤ α * mass (mu0 m) c +
        Real.exp (-β * Real.rpow (m : ℝ) ((1 : ℝ)/16)) := by sorry

end InterleavedUnitaryNOF.LowerBound
