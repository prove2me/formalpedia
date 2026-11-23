-- Prove2me | Theorems.Thm_InnovAlloc_Optimal_Supplement_theorem_2
-- name    : InnovAlloc.Optimal.Supplement.theorem_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-23T09:50:31.390074+00:00
-- url     : https://prove2.me/theorems/fb9fc120-e0f2-4023-a3a7-b2e1897a7676
-- title:
--   Theorem 2 — endogenous sharing: one-agent, one–two–one and one–two capacity regimes
-- statement:
--   Let $\alpha\in[0,1]$ and $a_0=6\sqrt2-8$. The principal chooses a common share in $(0,1)$ together with any nonnegative split summing to at most capacity $B$. Joint optimality is defined in the actual effort game: an equilibrium exists and every candidate equilibrium dominates every equilibrium under every alternative admissible share and allocation. Let $\gamma_m(B)=1/\sqrt B$, let $\gamma_d(\alpha,B)$ be the maximizing equal-investment share, and let $M(B),D(\alpha,B)$ be the corresponding optimized scalar profits. For every $B>2$, $\gamma_d$ is indeed a maximizer.
--
--   For $0<B\le1$, zero investment is jointly optimal at every admissible share and earns zero. The positive-investment rules apply on the full domain $B>1$:
--
--   1. If $\alpha\le a_0$, $(B,0)$ at share $\gamma_m(B)$ is jointly optimal for every $B>1$.
--   2. If $a_0<\alpha<1/2$, there exist finite real thresholds $2<L<H$. The one-agent allocation at $\gamma_m$ is jointly optimal on $1<B\le L$ and $B\ge H$; the equal split at $\gamma_d$ is jointly optimal on $L\le B\le H$. Moreover,
--
--   $$M(B)<D(\alpha,B)\iff L<B<H,\qquad D(\alpha,B)=M(B)\iff B=L\text{ or }B=H.$$
--
--   3. If $1/2\le\alpha\le1$, there exists a finite real threshold $T>2$. The one-agent allocation at $\gamma_m$ is jointly optimal on $1<B\le T$ and the equal split at $\gamma_d$ is jointly optimal on $B\ge T$. Moreover,
--
--   $$M(B)<D(\alpha,B)\iff T<B,\qquad D(\alpha,B)=M(B)\iff B=T.$$
--
--   These equivalences hold for all $B>1$. They give genuine diversification regions and exclude additional switches. At each switching threshold both named allocations are optimal; allocation uniqueness is not claimed. The boundary $\alpha=1/2$ is included with a finite switch, rather than only a limit comparison at infinite capacity.
--
--   This is a companion to the published fixed-share Theorem 1, supported by Propositions 4 and 5. It is not used in the proof of that goal.
--
--   Differences from the source:
--   - reading: The positive-allocation theorem does not repeat a capacity premise. → The positive-investment clauses quantify over B>1; the separate 0<B<=1 clause states zero-investment optimality.; reason: Footnote 10 on p. 18 explicitly separates the zero-profit regime; 1/sqrt(B) is admissible only above 1.
--   - encoding: The theorem describes switches as capacity increases. → Finite existential thresholds and exact sign/tie sets of the actual optimized profits specify every capacity above 1.; reason: The proof on pp. 41–43 studies the optimized difference and one connected positive region; the statement retains a nonempty middle interval, finite eventual dominance at alpha=1/2, and all tie boundaries.
--   - reading: The paper speaks of the optimal allocation and treats its equilibrium as determined. → Joint optimality compares every candidate equilibrium with every equilibrium at every allowed alternative common share and feasible split.; reason: This preserves the immutable base semantics and handles multiplicity at alpha=0 without excluding it.
-- source:
--   Gao, Fan, Huang & Chen, “Resource Allocation Among Competing Innovators”, SSRN preprint 3658157 (February 2021), p. 20, Theorem 2; p. 18 footnote 10; proof pp. 41–43

import Mathlib
import Definitions.Def_InnovAlloc_Optimal_Supplement_Endogenous
import Definitions.Def_InnovAlloc_Optimal_Supplement_Comparison

namespace InnovAlloc.Optimal.Supplement

/-- Theorem 2 (p. 20), with finite switching thresholds for the genuinely optimized
values, and joint optimality in the effort game. Footnote 10 supplies the B ≤ 1 regime. -/
theorem theorem_2 (α : ℝ) (hα0 : 0 ≤ α) (hα1 : α ≤ 1) :
    (∀ B : ℝ, 0 < B → B ≤ 1 → ∀ γ ∈ Set.Ioo (0 : ℝ) 1,
      IsJointOptimal α B γ 0 0 ∧
      ∀ x1 x2, IsEquilibrium α γ 0 0 x1 x2 →
        principalProfit α γ 0 0 x1 x2 = 0) ∧
    (∀ B : ℝ, 2 < B → IsDuoShare α B (gammaD α B)) ∧
    (α ≤ alphaLow → ∀ B : ℝ, 1 < B →
      IsJointOptimal α B (gammaM B) B 0) ∧
    (alphaLow < α → α < 1 / 2 →
      ∃ L H : ℝ, 2 < L ∧ L < H ∧
        ∀ B : ℝ, 1 < B →
          ((B ≤ L ∨ H ≤ B) → IsJointOptimal α B (gammaM B) B 0) ∧
          (B ∈ Set.Icc L H →
            IsJointOptimal α B (gammaD α B) (B / 2) (B / 2)) ∧
          (duoValue α B = monoValue B ↔ B = L ∨ B = H) ∧
          (monoValue B < duoValue α B ↔ B ∈ Set.Ioo L H)) ∧
    (1 / 2 ≤ α →
      ∃ T : ℝ, 2 < T ∧
        ∀ B : ℝ, 1 < B →
          (B ≤ T → IsJointOptimal α B (gammaM B) B 0) ∧
          (T ≤ B → IsJointOptimal α B (gammaD α B) (B / 2) (B / 2)) ∧
          (duoValue α B = monoValue B ↔ B = T) ∧
          (monoValue B < duoValue α B ↔ T < B)) := by sorry

end InnovAlloc.Optimal.Supplement
