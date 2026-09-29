-- Prove2me | Theorems.Thm_LassoDantzig_REConditions_candes_tao_correlation_bound
-- name    : LassoDantzig.REConditions.candes_tao_correlation_bound
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T10:22:08.143361+00:00
-- url     : https://prove2.me/theorems/52385515-aa69-48f6-a371-f3fa8c92759e
-- title:
--   Candès–Tao bound $\frac1{\sqrt n}|P_{01}X\delta_{J_k}|_2\le\frac{\theta_{s,2s}}{\sqrt{\phi_{\min}(2s)}}|\delta_{J_k}|_2$
-- statement:
--   Let $X\in\mathbb R^{n\times M}$, $s\ge1$, $\delta\in\mathbb R^M$, and let $J,J'$ be disjoint index sets with $|J|\le s$ and $|J'|\le2s$. Let $P$ be the orthogonal projector in $\mathbb R^n$ onto the span of the columns of $X_{J'}$. If $\phi_{\min}(2s)>0$, then
--
--   $$
--   \frac1{\sqrt n}\,|PX\delta_J|_2\ \le\ \frac{\theta_{s,2s}}{\sqrt{\phi_{\min}(2s)}}\,|\delta_J|_2 .
--   $$
--
--   In the proof of Lemma 4.1 (i) (with $m=s$) this is applied with $J=J_k$, $k\ge2$, and $J'=J_{01}$, replacing (A.2): the tail blocks are disjoint from $J_{01}$ and have at most $s$ elements, and $|J_{01}|\le2s$. The paper cites the bound from Candès and Tao without proof.
--
--   **Formalization Note** The hypotheses the paper leaves implicit — $J\cap J'=\emptyset$, $|J|\le s$, $|J'|\le2s$ and $\phi_{\min}(2s)>0$ (a consequence of Assumption 1 in the proof) — are explicit. $n\ge1$, $M\ge2$ are standing assumptions.
-- source:
--   Bickel, Ritov and Tsybakov, Simultaneous Analysis of Lasso and Dantzig Selector, arXiv:0801.1095v3, p. 20, Appendix A, proof of Lemma 4.1 (i), display after (A.3) (cf. Candès and Tao [7])

import Mathlib
import Definitions.Def_LassoDantzig_REConditions_RE
import Definitions.Def_LassoDantzig_REConditions_RestrictedEigenvalues

namespace LassoDantzig.REConditions

/-- The Candès–Tao bound used in the proof of **Lemma 4.1 (i)**, Bickel–Ritov–Tsybakov,
arXiv:0801.1095v3, Appendix A, p. 20 (display after (A.3), "cf. [7]"). If `J` and `J'` are
disjoint, `|J| ≤ s`, `|J'| ≤ 2s` and `φ_min(2s) > 0`, then for the orthogonal projector
`P_{J'}` onto the span of the columns of `X_{J'}`:
`(1/√n)|P_{J'} X δ_J|₂ ≤ (θ_{s,2s}/√φ_min(2s)) |δ_J|₂`. In the proof `J = J_k` (`k ≥ 2`) and
`J' = J01`. -/
theorem candes_tao_correlation_bound {n M : ℕ} (X : Matrix (Fin n) (Fin M) ℝ)
    (hn : 1 ≤ n) (hM : 2 ≤ M) (s : ℕ) (hs : 1 ≤ s)
    (δ : Fin M → ℝ) (J J' : Finset (Fin M)) (hdisj : Disjoint J J')
    (hJ : J.card ≤ s) (hJ' : J'.card ≤ 2 * s) (hφ : 0 < phiMin X (2 * s)) :
    1 / Real.sqrt n * projNorm X J' (X.mulVec (restrict δ J)) ≤
      theta X s (2 * s) / Real.sqrt (phiMin X (2 * s)) * l2On δ J := by sorry

end LassoDantzig.REConditions
