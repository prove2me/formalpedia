-- Prove2me | Theorems.Thm_MirrorBP_JEA_lemma_1
-- name    : MirrorBP.JEA.lemma_1
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-23T03:58:45.938849+00:00
-- url     : https://prove2.me/theorems/626e8e3f-682c-4a6b-92b8-588b41f64a8e
-- title:
--   Lemma 1, p. 18 (corrected: V₂ coefficient 1/K̃, not 1/(2K̃)) — one-period decomposition of MBP's suboptimality into V₁–V₄
-- statement:
--   Throughout, $V$ is a finite set of $m = |V| > 1$ nodes, $\mathcal T$ a finite set of demand types, each type $\tau$ has nonempty pick-up and drop-off neighborhoods $\mathcal P(\tau), \mathcal D(\tau) \subseteq V$, and the payoffs satisfy $|w_{j\tau k}| \le 1$ for $j \in \mathcal P(\tau)$, $k \in \mathcal D(\tau)$.
--
--   Let $\boldsymbol\phi$ be a rate vector, $K \ge 1$, $\mathbf q \in \Omega_K$ the current state and $\bar{\mathbf q}$ its normalization (9). Let $f$ be strictly increasing and continuously differentiable on $(0,\infty)$, let $F_1$ be an antiderivative of $f$ on $(0,\infty)$ and $F(\bar{\mathbf q}) = \sum_j F_1(\bar q_j)$. Let MBP use $f$ with any argmax tie-break, and write $\mathbf q'$ for the next state. Let $B$ bound $|f'|$ on the positive points of every interval $[\bar q_j - 1/\tilde K, \bar q_j + 1/\tilde K]$, $j \in V$. Then
--   $$W^{\mathrm{SPP}}(\boldsymbol\phi) - \mathbb E[v^{\mathrm{MBP}} \mid \mathbf q] \le \underbrace{\tilde K\big(F(\bar{\mathbf q}) - \mathbb E[F(\bar{\mathbf q}') \mid \mathbf q]\big)}_{\mathcal V_1} + \underbrace{\frac{B}{\tilde K}}_{\mathcal V_2} + \underbrace{\big(W^{\mathrm{SPP}}(\boldsymbol\phi) - g(\mathbf f(\bar{\mathbf q}))\big)}_{\mathcal V_3} + \underbrace{\mathbb 1\{\exists j : q_j = 0\}}_{\mathcal V_4},$$
--   where the expectations are over the type $\tau \sim \boldsymbol\phi$ and $\mathbb E[v^{\mathrm{MBP}} \mid \mathbf q] = \sum_\tau \phi_\tau\, w(\text{MBP decision})$.
--
--   Summed over periods, $\mathcal V_1$ telescopes; this is the drift-plus-penalty inequality behind Proposition 3.
--
--   The printed statement has $\frac{1}{2\tilde K}\max_j \max_{x} |f'(x)|$ as $\mathcal V_2$. That is false: with two nodes $a, b$, types $a \to b$ and $b \to a$, $w \equiv 1$, $\boldsymbol\phi = (\tfrac12,\tfrac12)$ (so $\alpha = \tfrac12$), $f$ from (8), $K = 100$, $\mathbf q = (50, 50)$, the left side is $0$ while the printed right side is $-0.00812$; with coefficient $1/\tilde K$ it is $+0.00042$. A move $j \to k$ changes two coordinates of $\bar{\mathbf q}$, so the second-order remainder is twice the one in the proof.
--
--   Differences from the source:
--   - generalization: max_{τ, j ∈ P(τ), k ∈ D(τ)} |w_{jτk}| = 1 → |w j τ k| ≤ 1 for j ∈ P τ, k ∈ D τ; reason: the scaling is 'without loss of generality' (p. 10); every instance with max |w| = 1 satisfies |w| ≤ 1.
--   - reading: type set 𝒯 (finiteness implicit) → [Fintype Ty]; reason: the model is 'a finite-state Markov chain' and SPP 'a linear program' with sums over 𝒯 (pp. 9, 15); Appendix C's remark on infinitely many types presupposes finitely many in the model.
--   - correction: V₂ = (1/(2K̃)) max_j max_{x ∈ [q̄_j − 1/K̃, q̄_j + 1/K̃]} |f′(x)| → V₂ with coefficient 1/K̃ (B / Kt); reason: the printed lemma is false: 2 nodes, types a→b and b→a, w ≡ 1, φ = (1/2, 1/2), f from (8), K = 100, q = (50, 50) give LHS 0 > RHS −0.00812 (missions/_checks/lemma1_counterexample.py).
--   - encoding: V₂'s maximum of |f′| over the intervals → any B with |deriv f x| ≤ B at every x > 0 in the intervals, V₂ = B / K̃; reason: equivalent to the maximum when it is finite; avoids a real sSup where the interval touches 0.
--   - encoding: f strictly increasing and C¹ on normalized queue lengths → StrictMonoOn f (Ioi 0), ContDiffOn ℝ 1 f (Ioi 0); reason: q̄ > 0 always; any such f on (0, 1] extends to (0, ∞).
--   - encoding: F the antiderivative of f (f = ∇F) → F(q̄) = Σ_j F₁(q̄_j) with F₁′ = f on (0, ∞); reason: f acts coordinatewise, so every antiderivative has this form up to an additive constant, which cancels in V₁.
--   - encoding: conditional expectations given q̄[t] → one-step sums Σ_τ φ_τ (…) at the fixed state q; reason: MBP is deterministic and Markov.
--   - encoding: K any → 1 ≤ K; reason: for K = 0, K̃ = 0 and q̄ = 0/0 is undefined.
--   - generalization: (j*, k*) = argmax_{j ∈ P(τ), k ∈ D(τ)} of the score → any tie-break sel with IsArgmaxSel; reason: the paper's argmax is some tie-break; the statement holds for every one.
-- source:
--   Kanoria, Qian, Blind Dynamic Resource Allocation in Closed Networks via Mirror Backpressure, arXiv:1903.02764v4, p. 18, Lemma 1, (17); Appendix B.1, appendix pp. 5–6 (PDF 38–39)

import Mathlib
import Definitions.Def_MirrorBP_JEA_Model
import Definitions.Def_MirrorBP_JEA_MBP
import Definitions.Def_MirrorBP_JEA_SPP

namespace MirrorBP.JEA

open Finset

theorem lemma_1 {V Ty : Type} [Fintype V] [DecidableEq V] [Fintype Ty] [DecidableEq Ty]
    (P D : Ty → Finset V) (w : V → Ty → V → ℝ)
    (hm : 1 < Fintype.card V) (hP : ∀ τ, (P τ).Nonempty) (hD : ∀ τ, (D τ).Nonempty)
    (hw : ∀ τ, ∀ j ∈ P τ, ∀ k ∈ D τ, |w j τ k| ≤ 1)
    (φ : Ty → ℝ) (hφ : IsRate φ) (K : ℕ) (hK : 1 ≤ K) (q : V → ℕ) (hq : q ∈ StateSpace V K)
    (f F₁ : ℝ → ℝ) (hf : StrictMonoOn f (Set.Ioi 0)) (hfC1 : ContDiffOn ℝ 1 f (Set.Ioi 0))
    (hF : ∀ x : ℝ, 0 < x → HasDerivAt F₁ (f x) x)
    (sel : (V → ℕ) → Ty → V × V) (hsel : IsArgmaxSel P D w f K sel) (B : ℝ)
    (hB : ∀ j, ∀ x ∈ Set.Icc (qbar K q j - 1 / Kt (Fintype.card V) K)
        (qbar K q j + 1 / Kt (Fintype.card V) K), 0 < x → |deriv f x| ≤ B) :
    Wspp P D w φ - ∑ τ, φ τ * pay w τ (mbpDecision w f K sel q τ)
      ≤ Kt (Fintype.card V) K * (Fpot F₁ (qbar K q)
            - ∑ τ, φ τ * Fpot F₁ (qbar K (step q (mbpDecision w f K sel q τ))))
        + B / Kt (Fintype.card V) K
        + (Wspp P D w φ - gDual P D w φ (fun j => f (qbar K q j)))
        + (if ∃ j, q j = 0 then (1 : ℝ) else 0) := by sorry

end MirrorBP.JEA
