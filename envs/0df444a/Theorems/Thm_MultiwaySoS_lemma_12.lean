-- Prove2me | Theorems.Thm_MultiwaySoS_lemma_12
-- name    : MultiwaySoS.lemma_12
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T03:18:49.274821+00:00
-- url     : https://prove2.me/theorems/9e6dfd94-8024-4a12-a822-58693ab4b38d
-- title:
--   Lemma 12 (corrected: exact value $2\sum_{\ell_m\ge2}\ell_mx_m\le2$) — drift of $\Phi$ under the randomized policy $\mathcal R(\lambda)$
-- statement:
--   Let $\bar\lambda$ satisfy GPG$_{\epsilon_0}$ with basis $\mathcal M_+$, let $\lambda\in\mathcal B_{\epsilon_0,TV}(\bar\lambda)$, and let $x$ be the optimal solution of $\mathrm{SPP}(\lambda)$ whose non-zero components are exactly $\mathcal M_+$. The randomized policy $\mathcal R(\lambda)$ (Definition 3, p.37) commits an item of type $i$ to configuration $m$ with probability $M_{im}x_m/\sum_{m^\prime}M_{im^\prime}x_{m^\prime}$. For every array of virtual queues $\mathscr Q$, if an item drawn from $\lambda$ is packed by $\mathcal R(\lambda)$,
--   $$\mathbb E_{\lambda,\mathcal R(\lambda)}[\Phi(\mathscr Q^\prime)-\Phi(\mathscr Q)]=\sum_i\lambda_i\sum_{m\in\mathcal M_+}\frac{M_{im}x_m}{\sum_{m^\prime}M_{im^\prime}x_{m^\prime}}\,\Delta\Phi_m(\mathscr Q_m,i)=2\sum_{m\in\mathcal M_+,\ \ell_m\ge2}\ell_mx_m .$$
--   In particular the expected change is at most $2$, with equality when $\mathcal M_+$ has no singleton configuration.
--
--   Differences from the source:
--   - correction: $\mathbb E_{\lambda,\mathcal R(\lambda)}[\Phi(\mathscr Q^\prime)-\Phi(\mathscr Q)]=2$ → $=2\sum_{m\in\mathcal M_+,\ \ell_m\ge2}\ell_mx_m$ (hence $\le2$); reason: with a singleton $b\in\mathcal M_+$ (instance $a=\{1,2\}$, $b=\{1\}$, $\bar\lambda=(2/3,1/3)$, $x=(1/3,1/3)$) the change is $2\cdot2\cdot\tfrac13=\tfrac43<2$; the proof only uses $\le2$ (p.47)
--   - generalization: a state encountered during the execution of Algorithm 2 → any integer array $\mathscr Q$; reason: the proof uses no property of reachable states
--   - reading: Definition 2 (GPG), clause 2 "with $\mathcal M_+$ as the basic activities", and clause 1 → the support of the solution is exactly $\mathcal M_+$, whose columns are linearly independent; clause 1 is not written; reason: basic activities are the non-zero components (p.4); clause 1 follows from linear independence
--   - reading: matching matrix $M\in\mathbb N^{n\times d}$, with an extension to general $M_{im}$ mentioned (§4, p.15) → $M_{im}\in\{0,1\}$, stored as the sets $\mathcal I(m)$; reason: §4 says "to keep exposition clear in this paper we focus on $M_{im}\in\{0,1\}$"; the potential (5) and Algorithm 2 are defined only for this case
--   - encoding: $\mathbb E_{\lambda,\mathcal R(\lambda)}[\Phi(\mathscr Q^\prime)-\Phi(\mathscr Q)]$ → $\sum_i\lambda_i\sum_{m\in\mathcal M_+}p_{im}\Delta\Phi_m(\mathscr Q_m,i)$ with $p_{im}=M_{im}x_m/\sum_{m^\prime}M_{im^\prime}x_{m^\prime}$ (Definition 3, p.37); reason: the definition of this expectation: committing to $m$ changes only $\Phi_m$, and $x_m=0$ outside $\mathcal M_+$
-- source:
--   Gupta, Greedy Algorithm for Multiway Matching with Bounded Regret, arXiv:2112.04622v3, Lemma 12, p.39; Definition 3, p.37

import Mathlib
import Definitions.Def_MultiwaySoS_Algorithm

namespace MultiwaySoS

/-- Lemma 12 (arXiv:2112.04622v3, p.39), with the exact value (corrected: `= 2` holds only when
`M₊` has no singleton configuration).

Let `λ̄` satisfy `GPG_{ϵ₀}` with basis `B = M₊`, let `λ ∈ B_{ϵ₀,TV}(λ̄)` and `x` the optimal solution
of (SPP(λ)) with basic activities `M₊`. The randomized policy `R(λ)` (Definition 3, p.37) commits an
item of type `i` to `m` with probability `M_im x_m / ∑_{m'} M_im' x_m'`. For every state `𝒬`, the
expected change of the sum-of-squares potential when an item drawn from `λ` is packed by `R(λ)` is
`E_{λ,R(λ)}[Φ(𝒬') − Φ(𝒬)] = 2 ∑_{m ∈ M₊, ℓ_m ≥ 2} ℓ_m x_m` (in particular `≤ 2`). -/
theorem lemma_12 {n d : ℕ} (I : Instance n d) (B : Finset (Fin d)) (σ : Fin d → List (Fin n))
    (hσ : IsCyclicOrder I σ) (lamBar : Fin n → ℝ) (ε₀ : ℝ) (xStar : Fin d → ℝ)
    (hG : IsGPG I lamBar ε₀ xStar B) (lam : Fin n → ℝ) (hlam : InTVBall ε₀ lamBar lam)
    (x : Fin d → ℝ) (hx : IsSPPOptimal I lam x) (hxB : ∀ m, x m ≠ 0 ↔ m ∈ B)
    (Q : Fin n → Fin d → ℤ) :
    ∑ i, lam i * ∑ m ∈ B, (I.M i m * x m / ∑ m', I.M i m' * x m') *
        ((deltaPhi I (σ m) m (fun j => Q j m) i : ℤ) : ℝ) =
      2 * ∑ m ∈ B.filter (fun m => 2 ≤ (I.conf m).card), ((I.conf m).card : ℝ) * x m := by sorry

end MultiwaySoS
