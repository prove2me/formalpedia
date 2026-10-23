-- Prove2me | Theorems.Thm_MirrorBP_JEA_lemma_3
-- name    : MirrorBP.JEA.lemma_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-23T03:58:47.600723+00:00
-- url     : https://prove2.me/theorems/2330bb12-b542-4209-a7cf-3fbc4ec477ae
-- title:
--   Lemma 3, p. 19 — V₂ + V₃ + V₄ ≤ Cm²/K̃ for the congestion function (8) once K ≥ poly(m, 1/α(φ)) (V₂ with the coefficient 1/K̃ of corrected Lemma 1)
-- statement:
--   There are a universal constant $C > 0$ and a polynomial bound $K_1 = c\,(m + 1/\alpha)^N$ such that the following holds. Let $V$ be a finite set of $m > 1$ nodes, $\mathcal T$ a finite type set with nonempty $\mathcal P(\tau), \mathcal D(\tau)$, $|w_{j\tau k}| \le 1$, and $\boldsymbol\phi$ a rate vector with $\alpha(\boldsymbol\phi) > 0$. For every $K \ge c\,(m + 1/\alpha(\boldsymbol\phi))^N$ and every $\mathbf q \in \Omega_K$, with $f$ the congestion function (8),
--   $$\mathcal V_2 + \mathcal V_3 + \mathcal V_4 \le \frac{C m^2}{\tilde K},$$
--   where $\mathcal V_2 = \frac{1}{\tilde K}\max_{j}\max_{x \in [\bar q_j - 1/\tilde K, \bar q_j + 1/\tilde K]} |f'(x)|$, $\mathcal V_3 = W^{\mathrm{SPP}}(\boldsymbol\phi) - g(\mathbf f(\bar{\mathbf q}))$ and $\mathcal V_4 = \mathbb 1\{\exists j: q_j = 0\}$. That is: some $B$ bounds $|f'|$ on the positive points of the intervals and $B/\tilde K + \mathcal V_3 + \mathcal V_4 \le Cm^2/\tilde K$.
--
--   Combined with Lemma 1 this bounds MBP's one-period suboptimality by the drift $\mathcal V_1$ plus $Cm^2/\tilde K$.
--
--   Differences from the source:
--   - generalization: max_{τ, j ∈ P(τ), k ∈ D(τ)} |w_{jτk}| = 1 → |w j τ k| ≤ 1 for j ∈ P τ, k ∈ D τ; reason: the scaling is 'without loss of generality' (p. 10); every instance with max |w| = 1 satisfies |w| ≤ 1.
--   - reading: type set 𝒯 (finiteness implicit) → [Fintype Ty]; reason: the model is 'a finite-state Markov chain' and SPP 'a linear program' with sums over 𝒯 (pp. 9, 15); Appendix C's remark on infinitely many types presupposes finitely many in the model.
--   - encoding: K₁ = poly(m, 1/α_min), C universal → ∃ C c N before every type and instance binder, K ≥ c (m + 1/α_min)^N; reason: a polynomial in (m, 1/α) with m ≥ 2 is bounded by c (m + 1/α)^N, and conversely; C, c, N do not depend on the instance.
--   - generalization: V₂ with coefficient 1/(2K̃) → V₂ with coefficient 1/K̃; reason: the stated bound is then stronger than the printed one (V₂ ≥ 0), and it matches corrected Lemma 1, so that Proposition 3 follows from the two.
--   - encoding: V₂'s maximum of |f′| over the intervals → ∃ B bounding |deriv f| at the positive points of the intervals, V₂ = B / K̃; reason: equivalent to the maximum when it is finite, which it is for K ≥ 2.
-- source:
--   Kanoria, Qian, Blind Dynamic Resource Allocation in Closed Networks via Mirror Backpressure, arXiv:1903.02764v4, p. 19, Lemma 3, (18)

import Mathlib
import Definitions.Def_MirrorBP_JEA_Model
import Definitions.Def_MirrorBP_JEA_MBP
import Definitions.Def_MirrorBP_JEA_SPP

namespace MirrorBP.JEA

open Finset

theorem lemma_3 :
    ∃ C : ℝ, 0 < C ∧ ∃ c : ℝ, ∃ N : ℕ,
      ∀ (V Ty : Type) [Fintype V] [DecidableEq V] [Fintype Ty] [DecidableEq Ty]
        (P D : Ty → Finset V) (w : V → Ty → V → ℝ) (φ : Ty → ℝ) (K : ℕ) (q : V → ℕ),
        1 < Fintype.card V → (∀ τ, (P τ).Nonempty) → (∀ τ, (D τ).Nonempty) →
        (∀ τ, ∀ j ∈ P τ, ∀ k ∈ D τ, |w j τ k| ≤ 1) →
        IsRate φ → 0 < alphaConn P D φ →
        c * ((Fintype.card V : ℝ) + 1 / alphaConn P D φ) ^ N ≤ (K : ℝ) →
        q ∈ StateSpace V K →
        ∃ B : ℝ,
          (∀ j, ∀ x ∈ Set.Icc (qbar K q j - 1 / Kt (Fintype.card V) K)
              (qbar K q j + 1 / Kt (Fintype.card V) K),
              0 < x → |deriv (fMBP (Fintype.card V)) x| ≤ B) ∧
          B / Kt (Fintype.card V) K
              + (Wspp P D w φ - gDual P D w φ (fun j => fMBP (Fintype.card V) (qbar K q j)))
              + (if ∃ j, q j = 0 then (1 : ℝ) else 0)
            ≤ C * (Fintype.card V : ℝ) ^ 2 / Kt (Fintype.card V) K := by sorry

end MirrorBP.JEA
