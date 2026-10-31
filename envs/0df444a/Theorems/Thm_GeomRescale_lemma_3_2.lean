-- Prove2me | Theorems.Thm_GeomRescale_lemma_3_2
-- name    : GeomRescale.lemma_3_2
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T04:14:48.983377+00:00
-- url     : https://prove2.me/theorems/d8c4070d-6496-427d-8228-578e7ca65aa6
-- title:
--   Lemma 3.2: $f_\mu$ is submodular and $B(f_\mu)$ grows with $\mu$
-- statement:
--   Let $f$ be submodular with $f(\emptyset) = 0$ and let $\mu \ge \max\{0, -f(V)\}$. Then $f_\mu$ is submodular. If $0 \in B(f_\mu)$, then $-\mu \le f(S)$ for every $S \subseteq V$. Furthermore, $B(f_\mu) \subseteq B(f_{\mu'})$ whenever $\mu \le \mu'$.
--
--   The second claim is the optimality certificate of the algorithm, and the third lets earlier bases survive a sliding step.
--
--   Differences from the source:
--   - generalization: $f$ integer valued (standing assumption of Section 3) → $f$ and $\mu$ real; reason: the proof uses no integrality; apply it to `fR f` and an integer $\mu$ for the page's statement
-- source:
--   Dadush, Végh & Zambelli, Geometric Rescaling Algorithms for Submodular Function Minimization, arXiv:1707.05065v4, Lemma 3.2, p.7

import Mathlib
import Definitions.Def_NonmonotoneSubmod_Shared_Submodular
import Definitions.Def_SchrijverSFM_Alg_Setting
import Definitions.Def_GeomRescale_enlarge

open NonmonotoneSubmod.Shared
open SchrijverSFM.Alg

namespace GeomRescale

/-- Lemma 3.2 (Dadush, Végh & Zambelli, Geometric Rescaling Algorithms for Submodular Function Minimization, arXiv:1707.05065v4, Lemma 3.2, p.7): for `μ ≥ max {0, −f(V)}`, `f_μ` is submodular; if
`0 ∈ B(f_μ)` then `−μ ≤ f(S)` for every `S ⊆ V`; and `B(f_μ) ⊆ B(f_μ′)` whenever `μ ≤ μ′`.

**Formalization Note.** `f` is real valued, as the proof allows, with `f(∅) = 0` (p.1). -/
theorem lemma_3_2 {n : ℕ} (f : Finset (Fin n) → ℝ) (hsub : Submodular f) (hf0 : f ∅ = 0)
    (μ : ℝ) (hμ : max 0 (-f Finset.univ) ≤ μ) :
    Submodular (enlarge f μ) ∧
      ((0 : Fin n → ℝ) ∈ baseB (enlarge f μ) → ∀ S, -μ ≤ f S) ∧
      ∀ μ' : ℝ, μ ≤ μ' → baseB (enlarge f μ) ⊆ baseB (enlarge f μ') := by sorry

end GeomRescale
