-- Prove2me | Theorems.Thm_GeomRescale_lemma_3_4
-- name    : GeomRescale.lemma_3_4
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T04:15:34.235982+00:00
-- url     : https://prove2.me/theorems/3ab04a9f-9dfc-4af9-a90f-c42c1aebff0e
-- title:
--   Lemma 3.4: $L_{f_\mu} \le 4L_f$
-- statement:
--   Let $f$ be submodular with $f(\emptyset) = 0$, let $\mu \ge \max\{0, -f(V)\}$ with $\mu = -f(W)$ for some $W \subseteq V$. Then
--
--   $$L_{f_\mu} \le 4 L_f.$$
--
--   So the enlargement does not change the complexity parameter by more than a constant factor.
--
--   Differences from the source:
--   - generalization: $f$ integer valued (standing assumption of Section 3) → $f$ and $\mu$ real; reason: the proof uses no integrality; apply it to `fR f` and an integer $\mu$ for the page's statement
-- source:
--   Dadush, Végh & Zambelli, Geometric Rescaling Algorithms for Submodular Function Minimization, arXiv:1707.05065v4, Lemma 3.4, p.7

import Mathlib
import Definitions.Def_NonmonotoneSubmod_Shared_Submodular
import Definitions.Def_GeomRescale_enlarge
import Definitions.Def_GeomRescale_Lone

open NonmonotoneSubmod.Shared
open SchrijverSFM.Alg

namespace GeomRescale

/-- Lemma 3.4 (Dadush, Végh & Zambelli, Geometric Rescaling Algorithms for Submodular Function Minimization, arXiv:1707.05065v4, Lemma 3.4, p.7): if `μ ≥ max {0, −f(V)}` and `μ = −f(W)` for some `W ⊆ V`,
then `L_{f_μ} ≤ 4L_f`. -/
theorem lemma_3_4 {n : ℕ} (f : Finset (Fin n) → ℝ) (hsub : Submodular f) (hf0 : f ∅ = 0)
    (μ : ℝ) (hμ : max 0 (-f Finset.univ) ≤ μ) (W : Finset (Fin n)) (hW : μ = -f W) :
    Lone (enlarge f μ) ≤ 4 * Lone f := by sorry

end GeomRescale
