-- Prove2me | Theorems.Thm_LEDPCount_thm_1_1_rmse_chebyshev
-- name    : LEDPCount.thm_1_1_rmse_chebyshev
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T04:08:05.458147+00:00
-- url     : https://prove2.me/theorems/529ce1ad-4f4a-440f-b441-de9268d46c49
-- title:
--   Proof of Theorem 1.1 — RMSE identity and the Chebyshev step
-- statement:
--   Let $H$ have $k$ vertices and $\ell\ge1$ edges, $n\ge k$, $\varepsilon\in(0,1]$ and $G$ a graph on $[n]$. For the estimate of LNC:
--   1. $\mathbb E\bigl[(\widehat f_H(G)-f_H(G))^2\bigr]=\mathrm{Var}\bigl[\widehat f_H(G)\bigr]$;
--   2. $\mathrm{Var}[\widehat f_H(G)]$ is finite and
--   $$
--   \Pr\Bigl[\bigl|\widehat f_H(G)-f_H(G)\bigr|\le\sqrt{3\,\mathrm{Var}[\widehat f_H(G)]}\Bigr]\ge\frac23.
--   $$
--
--   Differences from the source:
--   - encoding: Algorithm 1 for a pattern on k vertices and an n-vertex graph → n ≥ k assumed; reason: line 11's (n − k)! is undefined for n < k; Theorem 1.1's setting
--   - encoding: the second moment and Var[f̂_H(G)], real numbers → a lintegral and evariance in ℝ≥0∞, with evariance ≠ ⊤ stated and its real value used under the square root; reason: Lean convention; the source's variance is a finite real
-- source:
--   Chen–Peng, The Power of Interaction in Locally Edge-Private Subgraph Counting, arXiv:2611.05038 (held version, sha256 d18032b0…), proof of Theorem 1.1, accuracy, p.21 (PDF p.23)

import Mathlib
import Definitions.Def_LEDPCount_lnc
import Definitions.Def_LEDPCount_subgraphCount

namespace LEDPCount

open MeasureTheory ProbabilityTheory

/-- Proof of Theorem 1.1, RMSE identity and Chebyshev step (Chen–Peng, arXiv:2611.05038, held version sha256 d18032b0…, p.21, PDF p.23): for
a pattern with `ℓ ≥ 1` edges, `n ≥ k`, `ε ∈ (0, 1]` and every graph `G`,
1. `E[(f̂_H(G) − f_H(G))²] = Var[f̂_H(G)]`;
2. `Var[f̂_H(G)] < ∞` and `Pr[|f̂_H(G) − f_H(G)| ≤ √(3 Var[f̂_H(G)])] ≥ 2/3`.

**Formalization Note** The second moment is a `lintegral` and `Var` is `evariance`, both in
`ℝ≥0∞`. -/
theorem thm_1_1_rmse_chebyshev {k : ℕ} (H : SimpleGraph (Fin k)) [DecidableRel H.Adj]
    (hℓ : 1 ≤ H.edgeFinset.card) (n : ℕ) (hkn : k ≤ n) (ε : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (G : SimpleGraph (Fin n)) :
    ∫⁻ t, ENNReal.ofReal (((lnc H n ε).output t - subgraphCount H G) ^ 2)
        ∂((lnc H n ε).transcript G) =
      evariance (lnc H n ε).output ((lnc H n ε).transcript G) ∧
    evariance (lnc H n ε).output ((lnc H n ε).transcript G) ≠ ⊤ ∧
    ENNReal.ofReal (2 / 3) ≤
      (lnc H n ε).transcript G {t | |(lnc H n ε).output t - subgraphCount H G| ≤
        Real.sqrt (3 * (evariance (lnc H n ε).output ((lnc H n ε).transcript G)).toReal)} := by sorry

end LEDPCount
