-- Prove2me | Theorems.Thm_InfoLossLAR_WorstCase_RegevSketch_terminal_width_slack
-- name    : InfoLossLAR.WorstCase.RegevSketch.terminal_width_slack
-- status  : Proved
-- author  : @BoomShaKaLaaaKa
-- created : 2026-11-15T09:16:15.489214+00:00
-- url     : https://prove2.me/theorems/f607ad41-3957-411d-a7b9-ca67a44baf89
-- title:
--   Fixed-family DGS terminal width and smoothing slack
-- statement:
--   Fix a positive integer dimension $n$, an integer $n\times n$ matrix $B$, and a positive rational target width $r$ satisfying the exact threshold in the joint DGS contract. Write $q=q(n)$, $\sigma=\sigma(n)$, and $\eta=\eta_{\varepsilon(n)}(L(B))$ for the real value of the smoothing parameter used in that contract. Set
--
--   $$
--   w=\frac{r\sigma}{\sqrt{2}\sqrt n}.
--   $$
--
--   Then $w>0$ and $w\ge8\sqrt2\,q\eta$. If $\eta>0$, then $w>\sqrt2\,q\eta$. For the terminal amplitude width $a=\sigma/(2w\sqrt n)$, the reciprocal Fourier width and the squared source width satisfy
--
--   $$
--   \frac1{\sqrt2\,a}=r,\qquad w^2=\frac{r^2\sigma^2}{2n}.
--   $$
--
--   These identities check the fixed-family numerical slack for the last width-reduction step and show that the square of the source width is rational when $r$ is rational. The statement is algebraic and makes no claim that the BDD oracle, Gaussian-state preparation, or quantum sampler has been implemented.
--
--   **Formalization Note.** $\eta$ means the exact value computed by `smoothingParam` and the input module in the existing `DGSAt` definition. The theorem imposes no nonsingularity assumption because its conclusion is purely algebraic; interpreting $\eta$ as a lattice smoothing parameter and using the strict inequality requires the corresponding lattice conditions and positivity.
-- source:
--   Oded Regev, On Lattices, Learning with Errors, Random Linear Codes, and Cryptography, https://cims.nyu.edu/~regev/papers/qcrypto.pdf, Theorem 3.1 and Lemmas 3.3, 3.14, pp. 18–19 and 26–27. This is an explicit fixed-family terminal-step parameter identity, including the formal DGSAt threshold; it is not a verbatim theorem or an implementation of the cited algorithm.

import Definitions.Def_InfoLossLAR_RegevSketch_DGS
set_option autoImplicit false
open InfoLossLAR.WorstCase InfoLossLAR.WorstCase.RegevSketch

namespace InfoLossLAR.WorstCase.RegevSketch

theorem terminal_width_slack {n : ℕ} (B : Matrix (Fin n) (Fin n) ℤ)
    (r : ℚ) (hn : 0 < n) (hr : 0 < r)
    (hthreshold : dgsThreshold B ≤ (r : ℝ)) :
    let eta := RegevLWE.GaussConv.smoothingParam (inputModule B) (smoothingError n)
    let source := (r : ℝ)*(famσ n : ℝ)/(Real.sqrt 2*Real.sqrt n)
    0 < source ∧ 8*Real.sqrt 2*(famq n : ℝ)*eta ≤ source ∧
      (0 < eta → Real.sqrt 2*(famq n : ℝ)*eta < source) ∧
      1/(Real.sqrt 2*((famσ n : ℝ)/(2*source)/Real.sqrt n)) = (r : ℝ) ∧
      source^2 = (r : ℝ)^2*(famσ n : ℝ)^2/(2*(n : ℝ)) := by sorry

end InfoLossLAR.WorstCase.RegevSketch
