-- Prove2me | Theorems.Thm_HolonomicPositivity_Robust_lemma_5_4_scaling_case_II_2
-- name    : HolonomicPositivity.Robust.lemma_5_4_scaling_case_II_2
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-11T15:34:04.854235+00:00
-- url     : https://prove2.me/theorems/5ce6378f-0c6e-4f57-bdd6-7d7c906d874f
-- title:
--   Lemma 5.4, scaling in case II-2 — a scaling function S with S ≥ 0, B > 0, inequality (6) and C ≥ 0
-- statement:
--   Let $P, Q \in \mathbb{R}(x)$ and suppose $P$ has the Taylor expansion $P(x) = p_0 + p_1/x + p_2/x^2 + p_3/x^3 + O(x^{-4})$ at infinity (`HasTaylorExpansion`), $P(x) \ge -\tfrac13 - \tfrac{1}{9x^2} + O(x^{-3})$, $P(x) < 1 - \tfrac2x + O(x^{-2})$ (the first two clauses of condition (II) of Theorem 3.1), and the case hypothesis (II-2): $p_0 = -\tfrac13$, $p_1 > 0$ and $Q(x) \ge R_P(x) + O(x^{-2})$ with $R_P$ = `thresholdTwo`. Then there is $S \in \mathbb{R}(x)$ with $S \ge 0$, such that $B(x) := 1 - S(x+2)$ is eventually positive, $A(x)/(B(x)B(x-1))$ satisfies inequality (6) with $A(x) := B(x)S(x+1) + P(x)$, and $C(x) := A(x)S(x) + Q(x) \ge 0$ eventually (`scaledB`, `scaledA`, `scaledC`, `SatisfiesInequalitySix`; $\ge$ and $>$ for rational functions mean for all sufficiently large $x$).
--
--   This is the part of the proof of Lemma 5.4 (Hagihara, pp. 13–14, STOC 2027 submission 328) that treats the case (II-2): $p_0 = -\tfrac13$, $p_1 > 0$ and $Q(x) \ge R_P(x) + O(x^{-2})$ with $R_P$ = `thresholdTwo`; it is stated separately so that the proof of Lemma 5.4 can be split in three. The remaining clause of Lemma 5.4, the existence of $L$, follows from Lemma 5.3.
-- source:
--   Hagihara, F., Positivity Proofs for Third-Order Holonomic Sequences via Differences Scaled by Rational Functions, STOC 2027 submission 328, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/328.pdf (no DOI yet), pp. 13-14, proof of Lemma 5.4, case II-2

import Mathlib
import Definitions.Def_HolonomicPositivity_Robust_Comparison
import Definitions.Def_HolonomicPositivity_Robust_Conditions

namespace HolonomicPositivity.Robust

theorem lemma_5_4_scaling_case_II_2 (P Q : RatFunc ℝ) (p₀ p₁ p₂ p₃ : ℝ)
    (hT : HasTaylorExpansion P p₀ p₁ p₂ p₃)
    (hge : GeMod (ev P) (fun x => -(1 / 3) - 1 / (9 * x ^ 2)) (-3))
    (hlt : LtMod (ev P) (fun x => 1 - 2 / x) (-2))
    (hp1 : p₀ = -(1 / 3))
    (hp2 : 0 < p₁)
    (hq : GeMod (ev Q) (thresholdTwo p₁) (-2)) :
    ∃ S : RatFunc ℝ, EventuallyGE (ev S) (fun _ => 0) ∧ EventuallyGT (scaledB S) (fun _ => 0) ∧
      SatisfiesInequalitySix (scaledA P S) (scaledB S) ∧ EventuallyGE (scaledC P Q S) (fun _ => 0) := by
  sorry

end HolonomicPositivity.Robust
