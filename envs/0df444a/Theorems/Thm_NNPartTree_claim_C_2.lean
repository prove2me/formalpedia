-- Prove2me | Theorems.Thm_NNPartTree_claim_C_2
-- name    : NNPartTree.claim_C_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T11:09:22.618283+00:00
-- url     : https://prove2.me/theorems/4d96e120-0263-446c-b2bd-120943aa49a0
-- title:
--   Claim C.2, p.43 — a threshold $t^\prime>0$ with $\mathrm{err}/\mathrm{tail}\le 2S(G)$ and $\mathrm{tail}\ge 1/(4M_4)$
-- statement:
--   Let $G:\mathbb R^d\to\mathbb R_{\ge0}$ with $\mathbf E_{\mathcal D_Y}[G^2]=1$ and $\mathbf E_{\mathcal D_Y}[G^4]=M_4$. Then there is $t'>0$ such that
--   $$\mathrm{err}(G,t')\le 2S(G)\,\mathrm{tail}(G,t')\quad\text{and}\quad\mathrm{tail}(G,t')\ge\frac1{4M_4},$$
--   where $\mathrm{err}(G,t)$ is the error of the threshold cut $\mathrm{sign}(G-t)$ and $\mathrm{tail}(G,t)=\Pr_{\mathcal D_Y}[G\ge t]$.
--
--   The second clause is where the kurtosis controls the balance of the cut.
--
--   Differences from the source:
--   - encoding: err(G, t′)/tail(G, t′) ≤ 2·S(G) → err ≤ 2·S(G)·tail; reason: tail > 0 follows from the second clause, as M₄ ≥ 1
--   - encoding: G : ℝ^d → ℝ≥0, E[G⁴] = M₄, the bound with S(G) → G measurable, G(y)⁴ integrable, and the first clause conditional on |G(x)² − G(y)²| being integrable; reason: M₄ is a number as printed; for S(G) = ∞ the first clause is trivial while the Lean integral would read 0, and the second clause is still claimed
-- source:
--   Khanna, Padaki, Waingarten, Learning Partition Trees for Nearest Neighbor Search, arXiv:2607.09909 (held copy of 2026-11-03, sha256 d32992f2…), Claim C.2, p.43; proof pp.43–44

import Mathlib
import Definitions.Def_NNPartTree_Moments

open MeasureTheory

namespace NNPartTree

/-- **Claim C.2**, p.43. S. Khanna, A. Padaki, E. Waingarten, *Learning Partition Trees for Nearest Neighbor Search*, arXiv:2607.09909 (held copy of 2026-11-03, sha256 d32992f2…).

For `G ≥ 0` with `E_{D_Y}[G²] = 1` and `E_{D_Y}[G⁴] = M₄` there is `t′ > 0` with
`err(G, t′)/tail(G, t′) ≤ 2 S(G)` and `tail(G, t′) ≥ 1/(4M₄)`.

**Formalization Note.** The ratio is written without division, `tail(G, t′) > 0` following from the second clause (`M₄ ≥ 1`). `err(G, t)` is the
error of the threshold cut `sign(G − t)`. `M₄` is a real number, as printed. The first clause is conditional on `S(G)` being finite: for
`S(G) = ∞` it is trivial, while the Lean integral would read `0`. -/
theorem claim_C_2 {d : ℕ} (D : Measure (Pt d × Pt d)) [IsProbabilityMeasure D] (G : Pt d → ℝ)
    (hG : Measurable G) (hG0 : ∀ x, 0 ≤ G x)
    (h4 : Integrable (fun y => G y ^ 4) (marginalY D)) (h2 : ∫ y, G y ^ 2 ∂(marginalY D) = 1) :
    ∃ t : ℝ, 0 < t ∧
      (Integrable (fun z : Pt d × Pt d => |G z.1 ^ 2 - G z.2 ^ 2|) D →
        err D (thresholdCut G t) ≤ 2 * relaxedEnergy D G * tail D G t) ∧
      1 / (4 * ∫ y, G y ^ 4 ∂(marginalY D)) ≤ tail D G t := by sorry

end NNPartTree
