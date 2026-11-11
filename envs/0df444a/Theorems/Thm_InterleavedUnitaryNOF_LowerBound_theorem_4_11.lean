-- Prove2me | Theorems.Thm_InterleavedUnitaryNOF_LowerBound_theorem_4_11
-- name    : InterleavedUnitaryNOF.LowerBound.theorem_4_11
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T07:10:09.156613+00:00
-- url     : https://prove2.me/theorems/4d55c41d-3d72-4e08-9d90-880497a532d1
-- title:
--   Theorem 4.11 — AGL relative-error estimate, absolute value and 1/30
-- statement:
--   There is a universal $\kappa_0>0$. Let $A,B,C,D$ be independent normalized Haar matrices in $SU(m)$, $m\ge1$. For measurable Boolean $u,w:SU(m)^2\to\{0,1\}$ with $\mathbb E u,\mathbb E w\ge e^{-\kappa_0\sqrt m}$,
--
--   $$|\mathbb E[u(A,C)w(B,(ABC)^{-1})]-\mathbb E[u(A,C)w(B,D)]|\le\mathbb E[u]\mathbb E[w]/30.$$
--
--   This is the relative-error estimate restated from AGL in the canonical submission.
--
--   Differences from the source:
--   - encoding: positive matrix dimension and measurable Boolean functions on SU(m) powers → Fin m with NeZero m, normalized Borel Haar on the actual matrix group, and Bool indicators valued in ℝ; reason: these represent exactly the source objects, including m=1, without a discretization of the group
--   - encoding: the independent four-matrix expectation → the product of the two independent pair expectations; reason: independence gives exactly this equality, while the constrained term is actual three-matrix sampling
-- source:
--   Haoyu Wang, Pei Wu, Guangxu Yang, STOC 2027 submission #1513 (October 2026), Theorem 4.11, printed p.14 = PDF p.14; https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1513.pdf

import Mathlib
import Definitions.Def_InterleavedUnitaryNOF_LowerBound_Regularity

open MeasureTheory

namespace InterleavedUnitaryNOF.LowerBound

theorem theorem_4_11 : ∃ κ₀ : ℝ, 0 < κ₀ ∧
    ∀ (m : ℕ) [NeZero m] (u w : SU m × SU m → Bool),
      Measurable u → Measurable w →
      Real.exp (-κ₀*Real.sqrt m) ≤ pairAverage (haar m) (bval ∘ u) →
      Real.exp (-κ₀*Real.sqrt m) ≤ pairAverage (haar m) (bval ∘ w) →
      |productAverage (haar m) 1 (bval ∘ u) (bval ∘ w) -
        pairAverage (haar m) (bval ∘ u) * pairAverage (haar m) (bval ∘ w)| ≤
        pairAverage (haar m) (bval ∘ u) * pairAverage (haar m) (bval ∘ w)/30 := by sorry

end InterleavedUnitaryNOF.LowerBound
