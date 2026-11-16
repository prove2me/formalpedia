-- Prove2me | Theorems.Thm_MeanCertificates1424_Hardness_Supplement_theorem_6_1
-- name    : MeanCertificates1424.Hardness.Supplement.theorem_6_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T09:06:28.060731+00:00
-- url     : https://prove2.me/theorems/298d6dd2-be80-4798-9279-d5b4fa36e2ad
-- title:
--   Theorem 6.1 — exact recovery radius without audits
-- statement:
--   For the uniform mean without audits, the global minimax radius $R^*_\emptyset(G,b,L,\epsilon)$ is the infimum over all estimators of the worst-case error over all $L$-Lipschitz fields and all reports with at most $b$ vertices off by more than $\epsilon$. If $2b<n$, then
--   $$R^*_\emptyset(G,b,L,\epsilon)=\epsilon+\frac Ln\Psi_G(2b),$$
--   and the midpoint (2.1) of the observed certificate attains this value. If $2b\ge n$, the minimax error is infinite.
--
--   The radius is priced by the depth of the region that $2b$ replaced reports can jointly hide.
--
--   **Formalization Note** The radius is computed in $[0,\infty]$.
--
--   Differences from the source: none.
-- source:
--   chaomeng chen, Junhao Dong, STOC 2027 submission #1424 (October 2026), Theorem 6.1, printed p.19 (PDF p.21)

import Mathlib
import Definitions.Def_MeanCertificates1424_Hardness_Supplement_General

set_option autoImplicit false

open MeanCertificates1424.Hardness

namespace MeanCertificates1424.Hardness.Supplement

/-- Theorem 6.1, printed p.19 / PDF p.21. Uniform mean, no audits. If `2b < n` then
`R*_∅(G, b, L, ε) = ε + (L/n) Ψ_G(2b)` and the midpoint (2.1) attains it; if `2b ≥ n` the
minimax error is infinite. -/
theorem theorem_6_1 {n : ℕ} (G : SimpleGraph (Fin n)) (b : ℕ) (L ε : ℝ) (hn : 1 ≤ n)
    (hG : G.Connected) (hL : 0 < L) (hε : 0 ≤ ε) (hb : b ≤ n) :
    (2 * b < n →
      Psi G (2 * b) ≠ ⊤ ∧
      minimaxRadius G b L ε ∅ (uniformW n) =
        ENNReal.ofReal (ε + L / n * ((Psi G (2 * b)).toNat : ℝ)) ∧
      worstCase G b L ε ∅ (uniformW n) (midEstimator G b L ε ∅ (uniformW n)) =
        minimaxRadius G b L ε ∅ (uniformW n)) ∧
    (n ≤ 2 * b → minimaxRadius G b L ε ∅ (uniformW n) = ⊤) := by sorry

end MeanCertificates1424.Hardness.Supplement
