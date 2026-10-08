-- Prove2me | Theorems.Thm_NestedLogitVariants_Synergistic_lemma_14
-- name    : NestedLogitVariants.Synergistic.lemma_14
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-05T21:41:21.277437+00:00
-- url     : https://prove2.me/theorems/743d5c57-d022-484d-bd8d-ce2277bccc45
-- title:
--   Lemma 14, p. 43 — if γ_i > 1 for some nest, the factor α of (6) is at least 1
-- statement:
--   Consider an instance with fully-captured nests, positive revenues and $n \ge 2$ products per nest, and let
--
--   $$\alpha = \max_{i \in M,\ j = 2, \dots, n} \left\{\frac{R_i(N_{i,j-1})}{R_i(N_{ij})} \wedge \left(\frac{R_i(N_{ij})}{R_i(N_{i,j-1})}\, \frac{V_i(N_{ij})^{\gamma_i}}{V_i(N_{i,j-1})^{\gamma_i}}\right)\right\}$$
--
--   be the expression in (6). If $\gamma_i > 1$ for some nest $i$, then
--
--   $$\alpha \ge 1.$$
--
--   This is what lets the proof of Theorem 7 replace the coefficient $\alpha^1_{ik} \wedge (1 \vee \alpha^2_{ik})$ of (23) by $\alpha$.
--
--   **Formalization Note** The standing assumptions are those of the model (see the Model definition) and of §4: every nest is fully captured, $v_{i0} = 0$, and $\gamma_i > 1$ for some nest $i$ (p. 16). The positive revenues $r_{ij} > 0$ are the disclosed pin of this mission: they keep every denominator $R_i(N_{ij})$, $j \ge 1$, of (6) positive. The condition $n \ge 2$ makes the index range $j = 2, \dots, n$ of (6) nonempty. The number $\alpha$ is given together with the hypothesis that it is the greatest element of the set of terms of (6).
-- source:
--   Davis, Gallego, Topaloglu, Assortment optimization under variants of the nested logit model, revised manuscript of June 18, 2013 (published Oper. Res. 62(2), 2014, DOI 10.1287/opre.2014.1256), p. 43, Lemma 14

import Mathlib
import Definitions.Def_NestedLogitVariants_Synergistic_Factor

namespace NestedLogitVariants.Synergistic

/-- Lemma 14, p. 43: with `α` the expression in (6), if `γ_i > 1` for some nest `i`, then `α ≥ 1`. -/
theorem lemma_14 {ι : Type*} [Fintype ι] [DecidableEq ι] {n : ℕ} (I : Instance ι n)
    (hI : I.Standing) (hfc : ∀ i, I.vnp i = 0) (hsyn : ∃ i, 1 < I.γ i)
    (hr : ∀ i j, 0 < I.r i j) (hn : 2 ≤ n)
    (α : ℝ) (hα : IsGreatest (alphaTerms I) α) :
    1 ≤ α := by sorry

end NestedLogitVariants.Synergistic
