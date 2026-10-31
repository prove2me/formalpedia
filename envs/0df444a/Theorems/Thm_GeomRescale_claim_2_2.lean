-- Prove2me | Theorems.Thm_GeomRescale_claim_2_2
-- name    : GeomRescale.claim_2_2
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T04:15:31.197163+00:00
-- url     : https://prove2.me/theorems/93d9352c-ca64-44f0-83c6-ea76ab692c51
-- title:
--   Claim 2.2: the complexity parameters are equivalent
-- statement:
--   Let $f : 2^V \to \mathbb{R}$ be submodular with $f(\emptyset) = 0$. The maxima defining $L_f$ and $L_{f,2}$ are attained, and:
--
--   1. $L_{f,2} \le L_f \le \sqrt{n}\, L_{f,2}$;
--   2. $L_f = \Theta(F_f)$, in the form $F_f \le L_f \le 3F_f$;
--   3. for every $z \in B(f)$, $|z(v)| \le \alpha(v)$ for all $v \in V$; hence $L_f \le \|\alpha\|_1 = \alpha(V)$ and $L_{f,2} \le \|\alpha\|_2$;
--   4. $\alpha(v) \le 2F_f$ for all $v \in V$.
--
--   The running time depends on these parameters only up to a constant inside the logarithm.
--
--   Differences from the source:
--   - encoding: $L_f$, $L_{f,2}$ defined as maxima → `sSup`, with a conjunct stating that they are attained; reason: a real `sSup` of an unbounded set is $0$
--   - generalization: $L_f = \Theta(F_f)$ → $F_f \le L_f \le 3F_f$; reason: explicit constants imply the $\Theta$
-- source:
--   Dadush, Végh & Zambelli, Geometric Rescaling Algorithms for Submodular Function Minimization, arXiv:1707.05065v4, Claim 2.2, p.4

import Mathlib
import Definitions.Def_NonmonotoneSubmod_Shared_Submodular
import Definitions.Def_SchrijverSFM_Alg_Setting
import Definitions.Def_GeomRescale_norm1
import Definitions.Def_GeomRescale_norm2
import Definitions.Def_GeomRescale_Lone
import Definitions.Def_GeomRescale_Ltwo
import Definitions.Def_GeomRescale_Ff
import Definitions.Def_GeomRescale_alpha

open NonmonotoneSubmod.Shared
open SchrijverSFM.Alg

namespace GeomRescale

/-- Claim 2.2 (Dadush, Végh & Zambelli, Geometric Rescaling Algorithms for Submodular Function Minimization, arXiv:1707.05065v4, Claim 2.2, p.4), with the maxima defining `L_f`, `L_{f,2}` attained.
(i) `L_{f,2} ≤ L_f ≤ √n L_{f,2}`. (ii) `L_f = Θ(F_f)`, as `F_f ≤ L_f ≤ 3F_f`.
(iii) `|z(v)| ≤ α(v)` for `z ∈ B(f)`; hence `L_f ≤ ‖α‖₁ = α(V)` and `L_{f,2} ≤ ‖α‖₂`.
(iv) `α(v) ≤ 2F_f`.

**Formalization Note.** `Lone`, `Ltwo` are `sSup`s, so the first conjunct records that they are the
maxima of the page. The `Θ` of (ii) is written with its constants `1` and `3`. -/
theorem claim_2_2 {n : ℕ} (f : Finset (Fin n) → ℝ) (hsub : Submodular f) (hf0 : f ∅ = 0) :
    (IsGreatest (norm1 '' baseB f) (Lone f) ∧ IsGreatest (norm2 '' baseB f) (Ltwo f)) ∧
      (Ltwo f ≤ Lone f ∧ Lone f ≤ √(n : ℝ) * Ltwo f) ∧
      (Ff f ≤ Lone f ∧ Lone f ≤ 3 * Ff f) ∧
      ((∀ z ∈ baseB f, ∀ v, |z v| ≤ alpha f v) ∧
        Lone f ≤ norm1 (alpha f) ∧ norm1 (alpha f) = ∑ v, alpha f v ∧
        Ltwo f ≤ norm2 (alpha f)) ∧
      ∀ v, alpha f v ≤ 2 * Ff f := by sorry

end GeomRescale
