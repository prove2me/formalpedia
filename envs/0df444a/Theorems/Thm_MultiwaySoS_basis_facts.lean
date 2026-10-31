-- Prove2me | Theorems.Thm_MultiwaySoS_basis_facts
-- name    : MultiwaySoS.basis_facts
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T03:18:42.374648+00:00
-- url     : https://prove2.me/theorems/6044a5a6-366a-4029-9a57-fd16f59c3158
-- title:
--   p.23 — under GPG, $|\mathcal M_+|=n$ and $\alpha^*=r^\top_{\mathcal M_+}M^{-1}_{\mathcal M_+}$ is the unique dual optimum, optimal on the whole ball
-- statement:
--   Let $\lambda$ satisfy GPG$_\epsilon$ (Definition 2) with $\epsilon>0$, optimal basic feasible solution $x^*$ and basis $\mathcal M_+$. Then:
--
--   1. $|\mathcal M_+|=n$;
--   2. there is exactly one vector $\alpha^*\in\mathbb R^n$ with $\sum_iM_{im}\alpha^*_i=r_m$ for every $m\in\mathcal M_+$, namely $\alpha^*=r^\top_{\mathcal M_+}M^{-1}_{\mathcal M_+}$ (so $M_{\mathcal M_+}$ is invertible);
--   3. $\alpha^*$ is feasible for the dual and $\alpha^*\ge0$;
--   4. $\alpha^*$ is an optimal solution of $\mathrm{DSPP}(\hat\lambda)$ for every $\hat\lambda\in\mathcal B_{\epsilon,TV}(\lambda)$;
--   5. $\alpha^*$ is the unique optimal solution of $\mathrm{DSPP}(\lambda)$.
--
--   These are the facts about the basis that the proof of Theorem 2 uses: $\alpha^*$ is "the value of resources" pricing the virtual queues in Lemma 6, and $|\mathcal M_+|=n$ enters Lemma 13.
--
--   Differences from the source:
--   - reading: Definition 2 (GPG), clause 2 "with $\mathcal M_+$ as the basic activities", and clause 1 → the support of the solution is exactly $\mathcal M_+$, whose columns are linearly independent; clause 1 is not written; reason: basic activities are the non-zero components (p.4); clause 1 follows from linear independence
--   - encoding: $r^\top_{\mathcal M_+}M^{-1}_{\mathcal M_+}$ → the unique solution $\alpha$ of $\alpha\cdot M_m=r_m$ ($m\in\mathcal M_+$), with existence and uniqueness stated; reason: the same vector without a matrix inverse of a possibly non-square or singular matrix
--   - reading: Proposition 1 "if and only if" → only the forward facts (GPG implies the dual facts); reason: the converse is false (counterexample: $n=3$, $\lambda=(1/3,1/3,1/3)$, configurations $\{1,2\},\{1,3\}$ with reward $2$, $\{2\},\{3\}$ with reward $1$ and zero-reward singletons: the dual optimum $(1,1,1)$ is unique and optimal nearby, yet every optimal BFS has support of size 2), and the proof of Theorem 2 uses only the forward facts
-- source:
--   Gupta, Greedy Algorithm for Multiway Matching with Bounded Regret, arXiv:2112.04622v3, p.23, "As we point out in the proof of Proposition 1, r^⊤_{M+}M^{−1}_{M+} is the optimal solution to the dual"; p.35, "by our general position gap assumption M_{M+} is full rank"; p.46, "Since |M+| = n"; Proposition 1, p.16 (forward direction)

import Mathlib
import Definitions.Def_MultiwaySoS_Algorithm

namespace MultiwaySoS

/-- Basis facts under the General Position Gap (arXiv:2112.04622v3, p.23, "As we point out in the
proof of Proposition 1, r^⊤_{M₊} M^{−1}_{M₊} is the optimal solution to the dual (DSPP(λ)), and can be
thought of as the value of resources"; p.35, "by our general position gap assumption M_{M₊} is full
rank"; p.46, "Since |M₊| = n").

If `λ` satisfies `GPG_ε` with `ε > 0`, optimal basic solution `x*` and basis `B = M₊`, then
`|M₊| = n`, and there is exactly one vector `α*` with `α*·M_m = r_m` for every `m ∈ M₊`
(`α* = r^⊤_{M₊} M^{−1}_{M₊}`, so `M_{M₊}` is invertible); this `α*` is dual feasible and
nonnegative, it is an optimal solution of (DSPP(λ̂)) for every `λ̂ ∈ B_{ε,TV}(λ)`, and it is the
unique optimal solution of (DSPP(λ)).

**Formalization Note.** `α*` is characterized by the linear equations `α*·M_m = r_m` on `M₊`
instead of through a matrix inverse; existence and uniqueness of the solution is the
invertibility of the square matrix `M_{M₊}`. -/
theorem basis_facts {n d : ℕ} (I : Instance n d) (lam : Fin n → ℝ) (ε : ℝ) (xStar : Fin d → ℝ)
    (B : Finset (Fin d)) (hG : IsGPG I lam ε xStar B) (hε : 0 < ε) :
    B.card = n ∧
      ∃ α : Fin n → ℝ, (∀ m ∈ B, ∑ i, I.M i m * α i = I.r m) ∧
        (∀ β : Fin n → ℝ, (∀ m ∈ B, ∑ i, I.M i m * β i = I.r m) → β = α) ∧
        DSPPFeasible I α ∧ (∀ i, 0 ≤ α i) ∧
        (∀ q, InTVBall ε lam q → IsDSPPOptimal I q α) ∧
        (∀ β, IsDSPPOptimal I lam β → β = α) := by sorry

end MultiwaySoS
