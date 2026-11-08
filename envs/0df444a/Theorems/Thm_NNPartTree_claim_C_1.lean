-- Prove2me | Theorems.Thm_NNPartTree_claim_C_1
-- name    : NNPartTree.claim_C_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T11:09:14.844859+00:00
-- url     : https://prove2.me/theorems/7f21f484-7619-49a2-876c-45329ba79cf8
-- title:
--   Claim C.1, p.42 — $S(F)\le 8(\sqrt{R(F)}+R(F))$ when $\mathbf E[F^2]=1$
-- statement:
--   Let $\mathcal D$ be a law on pairs and $F:\mathbb R^d\to\mathbb R$ measurable with $\mathbf E_{\mathcal D_Y}[F^2]=1$ and $\mathrm{Var}_{\mathcal D_Y}[F]>0$, with $(F(x)-F(y))^2$ integrable. Then
--   $$S(F)\le 8\big(\sqrt{R(F)}+R(F)\big),\qquad S(F)=\mathbf E_{\mathcal D}[|F(x)^2-F(y)^2|].$$
--
--   This is the first step of the Cheeger-style rounding: it replaces the energy, a quadratic quantity, by the first-moment quantity $S$ that layer-cake integration can turn into a threshold cut.
--
--   Differences from the source:
--   - generalization: F with variance 1 on D_Y, under the standing normalization of App. C.1 (mean 0, variance 1, R(F) = E[(F(x) − F(y))²], p.42) → E[F(y)²] = 1 and Var[F(y)] > 0, R the ratio of Definition 5.2; reason: at mean 0, variance 1 the two agree, so the printed claim is an instance; this is the form the proof on p.45 applies to G, which has E[G²] = 1 and nonzero mean
--   - encoding: any F → F measurable, with (F(x) − F(y))² and F(y)² integrable; reason: Bochner integrals are 0 on non-integrable data; infinite energy makes the printed bound trivial
-- source:
--   Khanna, Padaki, Waingarten, Learning Partition Trees for Nearest Neighbor Search, arXiv:2607.09909 (held copy of 2026-11-03, sha256 d32992f2…), Claim C.1, p.42; proof p.43; application p.45

import Mathlib
import Definitions.Def_NNPartTree_Moments

open MeasureTheory

namespace NNPartTree

/-- **Claim C.1**, p.42. S. Khanna, A. Padaki, E. Waingarten, *Learning Partition Trees for Nearest Neighbor Search*, arXiv:2607.09909 (held copy of 2026-11-03, sha256 d32992f2…).

`S(F) ≤ 8 (√R(F) + R(F))` when `E_{D_Y}[F²] = 1` and `Var_{D_Y}[F] > 0`.

**Formalization Note.** The page says "with variance 1 on `D_Y`" under the standing normalization of
Appendix C.1 (p.42): `F` has mean `0` and variance `1` on `D_Y`, "for the remainder of the section", so that
`R(F) = E[(F(x) − F(y))²]`. This statement generalizes it: it assumes only `E[F²] = 1` and positive variance,
with `R(F)` the ratio of Definition 5.2. At mean `0`, variance `1` the two agree. The generalization is the form
the proof on p.45 uses, where the claim is applied to `G`, which has `E[G²] = 1` and nonzero mean. (Read without
the normalization, the printed claim would fail: `F(y) = 100 ± 1` with equal probability and `F(x) = F(y) + 1`
gives `R = 1`, `S = 201 > 16`.) Measurability and integrability hypotheses keep the Bochner integrals meaningful. -/
theorem claim_C_1 {d : ℕ} (D : Measure (Pt d × Pt d)) [IsProbabilityMeasure D] (F : Pt d → ℝ)
    (hF : Measurable F) (hE : Integrable (fun z : Pt d × Pt d => (F z.1 - F z.2) ^ 2) D)
    (hF2 : Integrable (fun y => F y ^ 2) (marginalY D)) (h2 : ∫ y, F y ^ 2 ∂(marginalY D) = 1)
    (hvar : 0 < varOn (marginalY D) F) :
    relaxedEnergy D F ≤ 8 * (Real.sqrt (energy D F) + energy D F) := by sorry

end NNPartTree
