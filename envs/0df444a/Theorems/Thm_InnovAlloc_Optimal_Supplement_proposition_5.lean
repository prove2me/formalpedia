-- Prove2me | Theorems.Thm_InnovAlloc_Optimal_Supplement_proposition_5
-- name    : InnovAlloc.Optimal.Supplement.proposition_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-23T09:49:55.965484+00:00
-- url     : https://prove2.me/theorems/518d78bc-bd74-44d0-9c43-f4e584a8b714
-- title:
--   Proposition 5 — equal-investment quasiconcavity, unique attainment and comparative statics
-- statement:
--   For every $\alpha\in[0,1]$ and $B>2$, the symmetric equal-investment principal profit $\gamma\mapsto\Pi_d(\alpha,\gamma,B)$ is quasiconcave on the full interval $(0,1)$. It has exactly one maximizing share $\gamma_d(\alpha,B)\in(0,1)$, and $2<\gamma_d(\alpha,B)B$. With $D$ and $F$ the optimized value and transformed objective,
--
--   $$D(\alpha,B)=F(\alpha,B,\gamma_d(\alpha,B)B)\ge F(\alpha,B,z)\quad(2<z<B).$$
--
--   For fixed $\alpha$, the maximizing share strictly decreases as $B$ increases through $(2,\infty)$. For fixed $B>2$, it strictly increases as $\alpha$ increases through $[0,1]$, including comparisons with either endpoint.
--
--   This provides the attained two-agent benchmark and the comparative statics needed for endogenous sharing. Quasiconcavity on $(0,1)$ is weak: profits are flat at zero for $\gamma B\le2$. The scalar objective is the symmetric benchmark, not an assertion that all effort equilibria are unique at $\alpha=0$.
--
--   Differences from the source:
--   - reading: The optimal share decreases in capacity and increases in alpha. → Strict antitonicity in capacity and strict monotonicity in alpha are quantified across the entire source domains.; reason: The statement is read literally as directional change between distinct parameters; both alpha endpoints are retained, though the appendix divides by alpha and 1-alpha.
--   - encoding: The appendix maximizes the transformed z objective on 2<z<B. → The chosen share is proved maximizing, its effective resource exceeds 2, and the transformed maximum is attained at z=gammaD*B.; reason: Attainment and uniqueness are conclusions; no supremum default or unproved choice property is used as an assumption.
-- source:
--   Gao, Fan, Huang & Chen, “Resource Allocation Among Competing Innovators”, SSRN preprint 3658157 (February 2021), p. 19, Proposition 5; proof pp. 39–41

import Mathlib
import Definitions.Def_InnovAlloc_Optimal_Supplement_Comparison

namespace InnovAlloc.Optimal.Supplement

/-- Proposition 5 (p. 19): weak quasiconcavity on the full share interval, unique
attainment, and comparative statics, retaining both endpoints of α ∈ [0,1]. -/
theorem proposition_5 :
    (∀ α B : ℝ, 0 ≤ α → α ≤ 1 → 2 < B →
      QuasiconcaveOn ℝ (Set.Ioo (0 : ℝ) 1) (fun γ => profitDuo α γ B) ∧
      (∃! γ, IsDuoShare α B γ) ∧
      IsDuoShare α B (gammaD α B) ∧
      2 < gammaD α B * B ∧
      duoValue α B = duoZProfit α B (gammaD α B * B) ∧
      (∀ z ∈ Set.Ioo (2 : ℝ) B, duoZProfit α B z ≤ duoValue α B)) ∧
    (∀ α : ℝ, 0 ≤ α → α ≤ 1 →
      StrictAntiOn (fun B => gammaD α B) (Set.Ioi (2 : ℝ))) ∧
    (∀ B : ℝ, 2 < B →
      StrictMonoOn (fun α => gammaD α B) (Set.Icc (0 : ℝ) 1)) := by sorry

end InnovAlloc.Optimal.Supplement
