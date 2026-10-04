-- Prove2me | Theorems.Thm_LassoDantzig_Oracle_decoupled_bound
-- name    : LassoDantzig.Oracle.decoupled_bound
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T11:10:39.424676+00:00
-- url     : https://prove2.me/theorems/507407a5-1a8b-4de7-8a2d-9de67a76728f
-- title:
--   Proof of Theorem 6.1 — the decoupled bound $\|\hat f_L-f\|_n^2\le\frac{b+1}{b-1}\|f_\beta-f\|_n^2+\frac{8b^2f_{\max}^2}{(b-1)\kappa^2}r^2\mathcal M(\beta)$
-- statement:
--   Under the hypotheses of the inequality before decoupling — $n\ge1$, $M\ge2$, $1\le s\le M$, nonzero column norms, $r>0$, $\varepsilon>0$, RE$(s,(3+4/\varepsilon)f_{\max}/f_{\min})$ with witness $\kappa>0$, noise vector $y-f$ in the event $\mathcal A$, a Lasso solution $\hat\beta$ for $y$ with $\hat f=X\hat\beta$, and $\beta$ with $\mathcal M(\beta)\le s$ in case (B.24) — for every $b>1$
--   $$\|\hat f-f\|_n^2\le\frac{b+1}{b-1}\|X\beta-f\|_n^2+\frac{8b^2f_{\max}^2}{(b-1)\kappa^2}\,r^2\,\mathcal M(\beta).$$
--
--   Taking $b=1+2/\varepsilon$ turns this into the oracle inequality (6.1) with $C(\varepsilon)=4(2+\varepsilon)^2/(\varepsilon(1+\varepsilon))$.
-- source:
--   Bickel, Ritov and Tsybakov, Simultaneous Analysis of Lasso and Dantzig Selector, arXiv:0801.1095v3, p. 26, Appendix B, proof of Theorem 6.1, last display

import Mathlib
import Definitions.Def_LassoDantzig_Oracle_Model

open MeasureTheory ProbabilityTheory

namespace LassoDantzig.Oracle

/-- **Decoupled bound in the proof of Theorem 6.1** (p. 26, last display). Under the hypotheses
of the inequality before decoupling (RE(s, (3 + 4/ε) f_max/f_min) with witness `κ > 0`, the event
`𝒜`, a Lasso solution `β̂` with `r > 0`, `𝓜(β) ≤ s`, case (B.24)), for every `b > 1`:
`‖f̂_L − f‖_n² ≤ (b + 1)/(b − 1) ‖f_β − f‖_n² + 8b² f_max² / ((b − 1)κ²) · r² 𝓜(β)`. -/
theorem decoupled_bound {n M : ℕ} (hn : 1 ≤ n) (hM : 2 ≤ M) (X : Matrix (Fin n) (Fin M) ℝ)
    (hcol : ∀ j, colNorm X j ≠ 0) (f y : Fin n → ℝ) (r : ℝ) (hr : 0 < r)
    (hA : NoiseBound X (fun i => y i - f i) r) (ε : ℝ) (hε : 0 < ε)
    (s : ℕ) (hs1 : 1 ≤ s) (hsM : s ≤ M) (κ : ℝ) (hκ : 0 < κ)
    (hRE : RE X s ((3 + 4 / ε) * fmax X / fmin X) κ)
    (βhat : Fin M → ℝ) (hL : IsLasso X y r βhat) (β : Fin M → ℝ) (hβs : sparsity β ≤ s)
    (hB24 : ε * empSq (fun i => X.mulVec β i - f i) <
      4 * r * ∑ j ∈ supp β, colNorm X j * |βhat j - β j|) :
    ∀ b : ℝ, 1 < b →
      empSq (fun i => X.mulVec βhat i - f i) ≤
        (b + 1) / (b - 1) * empSq (fun i => X.mulVec β i - f i) +
          8 * b ^ 2 * fmax X ^ 2 / ((b - 1) * κ ^ 2) * r ^ 2 * (sparsity β : ℝ) := by sorry

end LassoDantzig.Oracle
