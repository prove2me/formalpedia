-- Prove2me | Theorems.Thm_ImpulseGames_Verification_lemma2_3_controlled_process
-- name    : ImpulseGames.Verification.lemma2_3_controlled_process
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-04T03:04:11.500677+00:00
-- url     : https://prove2.me/theorems/5b74b3ee-d0db-4bcf-8676-ff536725084f
-- title:
--   Lemma 2.3 — representation (2.4), right-continuity, jumps (2.5), and $X$ stays in $\mathcal C_1\cap\mathcal C_2$
-- statement:
--   Let $x\in S$, let $\varphi_i=(\mathcal C_i,\xi_i)$ be strategies for $i\in\{1,2\}$, and let $\{Y^{\tilde\tau_k,x_k}\}_k$ be a realization of the construction of Definition 2.2, with controlled process $X$, exit time $\tau_S$, number of steps $\bar k$, intervention times $\tau_{i,n}$, impulses $\delta_{i,n}$ and pre-intervention states $X_{(\tau_{i,n})^-}$. Then for every $\omega$:
--
--   1. **Representation (2.4).** For every $k\le\bar k$ and every $s\ge\tilde\tau_k$ with, when $k<\bar k$, $s<\tilde\tau_{k+1}$:
--   $$X_s=Y^{\tilde\tau_k,x_k}_s .$$
--   2. **Continuity.** $X$ is right-continuous on $[0,\tau_S)$, and continuous at every $s<\tau_S$ that is not an intervention time $\tau_{i,n}<\tau_S$.
--   3. **Jumps (2.5).** For every $i$ and $n\ge1$ with $\tau_{i,n}<\tau_S$:
--   $$\delta_{i,n}=\xi_i\big(X_{(\tau_{i,n})^-}\big),\qquad X_{(\tau_{i,n})^-}\notin\mathcal C_i,$$
--   and, if no other intervention follows at the same instant, $X_{\tau_{i,n}}=\Gamma^i\big(X_{(\tau_{i,n})^-},\delta_{i,n}\big)$.
--   4. **No exit.** $X_s\in\mathcal C_1\cap\mathcal C_2$ for every $s\in\,]0,\tau_S[$ that is not an intervention time.
--
--   This lemma makes precise the informal rules (2.2): each player intervenes exactly when the state leaves her continuation set. It gives the properties (3.8) used in the proof of the verification theorem.
--
--   **Formalization Note.** Several clauses of the printed lemma fail at simultaneous or boundary interventions, which the paper allows (Remark 2.8), and are stated here in corrected form. (a) The page has $X_{(\tau_{i,k})^-}\in\partial\mathcal C_i$; when player 2 acts immediately after player 1 has moved the state deep outside $\mathcal C_2$, or at time 0 when $x\notin\bar{\mathcal C}_i$, that state is outside $\bar{\mathcal C}_i$; what holds and what the proof of Theorem 3.3 uses is $\notin\mathcal C_i$. (b) $X_{\tau_{i,k}}=\Gamma^i(\cdot)$ holds only when no further simultaneous intervention follows, since otherwise $X$ at that instant is the state after the last one; the condition is $\tilde\tau_{\eta(i,n)}<\tilde\tau_{\eta(i,n)+1}$. (c) "Never exits" holds at times that are not intervention times and $s>0$: at $s=0$ with $x\in\partial\mathcal C_i$, or right after a jump onto $\partial\mathcal C_i$, $X_s\notin\mathcal C_i$ is possible. (d) "Discontinuous at $\tau_{i,k}$" means "may jump" ($\Gamma^i(y,\delta)=y$ is allowed) and is not stated; the jump relation is (2.5). (e) Continuity statements are restricted to $[0,\tau_S)$; on $\{\bar k=\infty\}$, $X$ after $\tau_S$ is the paper's convention $\lim_k\tilde X^k$ and is not used. "Satisfies Equation (2.1) between jumps" is the representation (2.4) combined with the fact that each piece solves (2.1).
-- source:
--   Aïd et al. (2020), Math. Oper. Res. 45(1), accepted manuscript, Lemma 2.3 (p. 5)

import Mathlib
import Definitions.Def_ImpulseGames_Verification_Game

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal

namespace ImpulseGames.Verification

/-- Lemma 2.3 (properties of the controlled process), pathwise for every realization:
(2.4) the representation through the diffusion pieces; right-continuity before `τ_S` and
continuity off the intervention times; (2.5) at the `n`-th intervention of player `i` the
impulse is `ξ_i` of the pre-intervention state, that state lies outside `C_i`, and, when no
further intervention happens at the same instant, `X_{τ_{i,n}} = Γ_i(X_{(τ_{i,n})^-}, δ_{i,n})`;
and `X` stays in `C_1 ∩ C_2` at all times of `]0, τ_S[` that are not intervention times. -/
theorem lemma2_3_controlled_process {d k : ℕ} {Ω : Type*} [m : MeasurableSpace Ω]
    (P : Measure Ω) (𝔽 : Filtration ℝ≥0 m) (W : ℝ≥0 → Ω → (Fin k → ℝ))
    (hW : IsBrownianBasis P 𝔽 W) (G : Game d k) (hG : G.Standing)
    (x : State d) (hx : x ∈ G.S) (π : Profile G) (hπ : ∀ i, IsStrategy G i (π.C i) (π.ξ i))
    (Y : ℕ → ℝ≥0 → Ω → State d) (hY : IsRealization P 𝔽 W G x π Y) (ω : Ω) :
    -- (2.4)
    (∀ (n : ℕ) (s : ℝ≥0), (n : ℕ∞) ≤ kbar G x π (pathOf Y ω) →
      (stage G x π (pathOf Y ω) n).time ≤ (s : ℝ≥0∞) →
      ((n : ℕ∞) < kbar G x π (pathOf Y ω) →
        (s : ℝ≥0∞) < (stage G x π (pathOf Y ω) (n + 1)).time) →
      ctrl G x π (pathOf Y ω) s = Y n s ω) ∧
    -- right-continuity, and continuity off the intervention times
    (∀ s : ℝ≥0, (s : ℝ≥0∞) < exitTime G x π (pathOf Y ω) →
      ContinuousWithinAt (ctrl G x π (pathOf Y ω)) (Set.Ici s) s) ∧
    (∀ s : ℝ≥0, (s : ℝ≥0∞) < exitTime G x π (pathOf Y ω) →
      (s : ℝ≥0∞) ∉ interventionTimes G x π (pathOf Y ω) →
      ContinuousAt (ctrl G x π (pathOf Y ω)) s) ∧
    -- (2.5)
    (∀ (i : Player) (n : ℕ), 1 ≤ n →
      interTime G x π (pathOf Y ω) i n < exitTime G x π (pathOf Y ω) →
      impulse G x π (pathOf Y ω) i n = π.ξ i (preState G x π (pathOf Y ω) i n) ∧
      preState G x π (pathOf Y ω) i n ∉ π.C i ∧
      ((stage G x π (pathOf Y ω) (eta G x π (pathOf Y ω) i n)).time <
          (stage G x π (pathOf Y ω) (eta G x π (pathOf Y ω) i n + 1)).time →
        ctrl G x π (pathOf Y ω) (interTime G x π (pathOf Y ω) i n).toNNReal =
          G.Γ i (preState G x π (pathOf Y ω) i n) (impulse G x π (pathOf Y ω) i n))) ∧
    -- X never exits C₁ ∩ C₂
    (∀ s : ℝ≥0, 0 < s → (s : ℝ≥0∞) < exitTime G x π (pathOf Y ω) →
      (s : ℝ≥0∞) ∉ interventionTimes G x π (pathOf Y ω) →
      ctrl G x π (pathOf Y ω) s ∈ π.C .one ∩ π.C .two) := by sorry

end ImpulseGames.Verification
