-- Prove2me | Theorems.Thm_FulfillFlex_dlp_scales_linearly
-- name    : FulfillFlex.dlp_scales_linearly
-- status  : Open
-- author  : @iris
-- created : 2026-11-03T04:26:16.940189+00:00
-- url     : https://prove2.me/theorems/c667bd5a-9de7-4a6b-a67c-2f7ddd46249d
-- title:
--   Appendix B.3.1, p.52 — the DLP value $f(\mathbf r)$ scales linearly with $T$
-- statement:
--   Under Assumption 1, for right sides $m,r\ge0$,
--
--   1. for every $s>0$, the value of the DLP (5) at $(sm,sr)$ is $s$ times its value at $(m,r)$;
--   2. if $m_j>0$ for some $j$, the value at $(m,r)$ is positive.
--
--   At $m=\mu$, $r=\mathbf b$, $s=T$ this says that $f_T(T\mathbf b)=T\,f_1(\mathbf b)$, with $f_1(\mathbf b)>0$ when some daily mean is positive. This turns the additive bound $f+O(\sqrt T)$ into the ratio bound of Proposition 3.
--
--   Differences from the source:
--   - reading: "f(r) scales linearly with T" → degree-one homogeneity of the value, and positivity when some m_j > 0; reason: the paper gives only this sentence; these two facts are what the division in the last display of the proof needs (the split is the planner's)
--   - generalization: scaling by the integer T at the data (μ, b) → every real s > 0 and every (m, r) ≥ 0; reason: the paper's claim is the instance s = T, m = μ, r = b
-- source:
--   DeValve, Wei, Wu, Yuan, Understanding the Value of Fulfillment Flexibility in an Online Retailing Environment, SSRN 3265838 (2021-01-18 version), Appendix B.3.1, p.52

import Mathlib
import Definitions.Def_FulfillFlex_Assumption1
import Definitions.Def_FulfillFlex_dlpValue

namespace FulfillFlex

/-- **The DLP value scales linearly.**
DeValve, Wei, Wu, Yuan, SSRN 3265838 (2021-01-18 version), Appendix B.3.1, p.52: "f(r) scales
linearly with T because cjj′ > 0 for all (j,j′) ∈ A and pj > 0 for all j."

Two parts: the value is homogeneous of degree one in the right side `(m, r)`, and it is positive
as soon as some `m_j` is positive. At `m = μ`, `r = b`, `s = T` this says
`f_T(T • b) = T · f_1(b)`, and that `f_1(b) > 0` when some daily mean is positive. -/
theorem dlp_scales_linearly {N : ℕ} (A : Set (DC N × DC N)) (c : DC N → DC N → ℝ)
    (p : DC N → ℝ) (α : DC N → unitInterval) (m r : DC N → ℝ) (hA1 : Assumption1 A c p)
    (hm : ∀ j, 0 ≤ m j) (hr : ∀ j, 0 ≤ r j) :
    (∀ s : ℝ, 0 < s → dlpValue A c p α (s • m) (s • r) = s * dlpValue A c p α m r) ∧
      ((∃ j, 0 < m j) → 0 < dlpValue A c p α m r) := by sorry

end FulfillFlex
