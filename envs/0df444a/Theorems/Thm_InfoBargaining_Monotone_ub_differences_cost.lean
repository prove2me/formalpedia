-- Prove2me | Theorems.Thm_InfoBargaining_Monotone_ub_differences_cost
-- name    : InfoBargaining.Monotone.ub_differences_cost
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T22:58:39.145583+00:00
-- url     : https://prove2.me/theorems/8687419c-df56-4c5a-bac2-afe542850a86
-- title:
--   Proof of Proposition 1, p. 30 — ∂²U_b/∂c∂α = θ_b ∂G(c, α)/∂α: increasing differences in (α, c) for c ≤ û, decreasing for c ≥ û
-- statement:
--   Fix $\theta_b\in(0,1)$ and write $U_b(\alpha;c)=\theta_b A(\alpha,c)-k(\alpha)$ for the buyer's objective (6) at seller cost $c$. Then:
--
--   1. $U_b$ has increasing differences in $(\alpha,c)$ on $[\underline\alpha,\bar\alpha]\times(-\infty,\hat u]$: for all $c<c'\le\hat u$, the map $\alpha\mapsto U_b(\alpha;c')-U_b(\alpha;c)$ is nondecreasing on $[\underline\alpha,\bar\alpha]$;
--   2. $U_b$ has decreasing differences in $(\alpha,c)$ on $[\underline\alpha,\bar\alpha]\times[\hat u,\infty)$: for all $\underline\alpha\le\alpha\le\alpha'\le\bar\alpha$ and $\hat u\le c\le c'$,
--   $$U_b(\alpha';c')-U_b(\alpha';c)\ \le\ U_b(\alpha;c')-U_b(\alpha;c).$$
--
--   This is the discrete form of the paper's computation $\partial^2U_b/\partial c\,\partial\alpha=\theta_b\,\partial G(c,\alpha)/\partial\alpha$, positive for $c<\hat u$ and negative for $c>\hat u$ by (1). With Topkis's theorem it gives the second part of Proposition 1: $\alpha^*$ rises with $c$ below $\hat u$ and falls with $c$ above it.
--
--   **Formalization Note** Part 1 uses the platform definition `Supermodularity.Monotonicity.IncreasingDifferencesOn` with the section set $[\underline\alpha,\bar\alpha]\times(-\infty,\hat u]$; part 2 is written out as an explicit inequality. Both include $c=\hat u$, where the cross effect vanishes. The inequalities are weak because the prior may have no density.
-- source:
--   Guo, Gathering Information before Negotiation, SSRN 3930651 (manuscript of 15 Feb 2022), p. 30, Appendix, proof of Proposition 1, fourth and fifth sentences

import Mathlib
import Definitions.Def_InfoBargaining_Monotone_Setting
import Definitions.Def_Supermodularity_Monotonicity_IncreasingDifferencesOn

namespace InfoBargaining.Monotone

/-- Proof of Proposition 1, p. 30, fourth–fifth sentences: for `θ_b ∈ (0, 1)`, `U_b` has
increasing differences in `(α, c)` on `[αlo, αhi] × (-∞, û]` and decreasing differences in
`(α, c)` on `[αlo, αhi] × [û, ∞)` (the cross-partial `∂²U_b/∂c∂α = θ_b ∂G(c, α)/∂α` is
nonnegative for `c < û` and nonpositive for `c > û`). -/
theorem ub_differences_cost (M : Model) {θb : ℝ} (hθb : θb ∈ Set.Ioo (0 : ℝ) 1) :
    Supermodularity.Monotonicity.IncreasingDifferencesOn
      (fun α c => M.Ub θb c α) (Set.Icc M.αlo M.αhi ×ˢ Set.Iic M.uhat) ∧
    ∀ α ∈ Set.Icc M.αlo M.αhi, ∀ α' ∈ Set.Icc M.αlo M.αhi, α ≤ α' →
      ∀ c c' : ℝ, M.uhat ≤ c → c ≤ c' →
        M.Ub θb c' α' - M.Ub θb c α' ≤ M.Ub θb c' α - M.Ub θb c α := by sorry

end InfoBargaining.Monotone
