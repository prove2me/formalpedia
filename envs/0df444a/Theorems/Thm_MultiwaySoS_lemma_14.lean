-- Prove2me | Theorems.Thm_MultiwaySoS_lemma_14
-- name    : MultiwaySoS.lemma_14
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T03:18:55.191098+00:00
-- url     : https://prove2.me/theorems/51ee500e-96fa-40d0-a8ae-de08724c1e26
-- title:
--   Lemma 14 (Drift Lemma) — a hybrid policy with $\mathbb E[\Delta\Phi]\le-\delta\sqrt{\Phi}/B$ dominating SS
-- statement:
--   Let $\bar\lambda$ satisfy GPG$_{\epsilon_0}$ with basis $\mathcal M_+$, let $0<\delta\le\epsilon_0$ and $B=2n^2$. Let $\mathscr Q$ be an array of virtual queues with $\Phi(\mathscr Q)\ge4B^2/\delta^2$, into which an item of type drawn from $\lambda\in\mathcal B_{\epsilon_0-\delta,TV}(\bar\lambda)$ has to be packed. Then there is a policy $\mathrm{Hyb}(\lambda,\mathscr Q)$, a stochastic matrix $(p_{im})$ committing type $i$ only to configurations $m\in\mathcal M_+$ with $i\in\mathcal I(m)$, such that
--   $$\mathbb E_{\lambda,\mathrm{SS}}[\Phi(\mathscr Q^\prime)-\Phi(\mathscr Q)]\le\mathbb E_{\lambda,\mathrm{Hyb}(\lambda,\mathscr Q)}[\Phi(\mathscr Q^\prime)-\Phi(\mathscr Q)]\le-\frac{\delta\sqrt{\Phi(\mathscr Q)}}{B}.$$
--   Here $\mathbb E_{\lambda,p}[\cdot]=\sum_i\lambda_i\sum_mp_{im}\Delta\Phi_m(\mathscr Q_m,i)$, and $\mathbb E_{\lambda,\mathrm{SS}}$ uses any minimizing choice of SS.
--
--   Differences from the source:
--   - generalization: $0<\delta<\epsilon_0$ (Assumption 2, Theorem 2) → $0<\delta\le\epsilon_0$; reason: p.17 (example 2) and p.18 use $\delta=\epsilon_0$; the range contains the printed one
--   - generalization: a state of the virtual queues → any integer array $\mathscr Q$; reason: the proof uses no property of reachable states
--   - encoding: $\mathbb E_{\lambda,\mathrm{SS}}$ with the arg min of Algorithm 2 → the inequality for every choice function $g$ picking a minimizer of $\Delta\Phi_m(\mathscr Q_m,i)$ over $m\in\mathcal M_+$ containing $i$; reason: ties are arbitrary; every minimizing choice has the same expected change
--   - reading: Definition 2 (GPG), clause 2 "with $\mathcal M_+$ as the basic activities", and clause 1 → the support of the solution is exactly $\mathcal M_+$, whose columns are linearly independent; clause 1 is not written; reason: basic activities are the non-zero components (p.4); clause 1 follows from linear independence
--   - reading: matching matrix $M\in\mathbb N^{n\times d}$, with an extension to general $M_{im}$ mentioned (§4, p.15) → $M_{im}\in\{0,1\}$, stored as the sets $\mathcal I(m)$; reason: §4 says "to keep exposition clear in this paper we focus on $M_{im}\in\{0,1\}$"; the potential (5) and Algorithm 2 are defined only for this case
--   - encoding: a policy $\mathrm{Hyb}(\lambda,\mathscr Q)$, with $\mathbb E_{\lambda,\mathrm{Hyb}}[\Phi(\mathscr Q^\prime)-\Phi(\mathscr Q)]$ → a stochastic matrix $p_{im}$ supported on $\{m\in\mathcal M_+: i\in\mathcal I(m)\}$, chosen after $\lambda,\mathscr Q$, with expectation $\sum_i\lambda_i\sum_mp_{im}\Delta\Phi_m(\mathscr Q_m,i)$; reason: the policy of p.46 is such a matrix, and the conclusion only reads its one-step expected change
-- source:
--   Gupta, Greedy Algorithm for Multiway Matching with Bounded Regret, arXiv:2112.04622v3, Lemma 14, p.40; definition of Hyb, proof of Lemma 14, p.46

import Mathlib
import Definitions.Def_MultiwaySoS_Algorithm

namespace MultiwaySoS

/-- Lemma 14, Drift Lemma (arXiv:2112.04622v3, p.40).

Let `λ̄` satisfy `GPG_{ϵ₀}` with basis `B = M₊`, `0 < δ ≤ ϵ₀`, `Bc := 2n²`, and let `𝒬` be a state with
`Φ(𝒬) ≥ 4Bc²/δ²` into which an item of type drawn from `λ ∈ B_{ϵ₀−δ,TV}(λ̄)` has to be packed. Then
there is a policy `Hyb(λ, 𝒬)` — a stochastic matrix `p i m` committing type `i` to `m ∈ M₊` with
`i ∈ I(m)` — such that
`E_{λ,SS}[Φ(𝒬') − Φ(𝒬)] ≤ E_{λ,Hyb(λ,𝒬)}[Φ(𝒬') − Φ(𝒬)] ≤ −δ√Φ(𝒬)/Bc`.

**Formalization Note.** `E_{λ,SS}` is `∑_i λ_i ΔΦ_{g(i)}(𝒬_{g(i)}, i)` for every arg-min choice `g`
of SS; `E_{λ,p}` is `∑_i λ_i ∑_m p_im ΔΦ_m(𝒬_m, i)`. -/
theorem lemma_14 {n d : ℕ} (I : Instance n d) (B : Finset (Fin d)) (σ : Fin d → List (Fin n))
    (hσ : IsCyclicOrder I σ) (lamBar : Fin n → ℝ) (ε₀ δ : ℝ) (xStar : Fin d → ℝ)
    (hG : IsGPG I lamBar ε₀ xStar B) (hδ : 0 < δ) (hδε : δ ≤ ε₀) (lam : Fin n → ℝ)
    (hlam : InTVBall (ε₀ - δ) lamBar lam) (Q : Fin n → Fin d → ℤ)
    (hΦ : 4 * (2 * (n : ℝ) ^ 2) ^ 2 / δ ^ 2 ≤ ((Phi B σ Q : ℤ) : ℝ)) :
    ∃ p : Fin n → Fin d → ℝ, (∀ i m, 0 ≤ p i m) ∧ (∀ i, ∑ m, p i m = 1) ∧
      (∀ i m, p i m ≠ 0 → m ∈ B ∧ i ∈ I.conf m) ∧
      (∀ g : Fin n → Fin d, (∀ i, g i ∈ B ∧ i ∈ I.conf (g i) ∧ ∀ m ∈ B, i ∈ I.conf m →
          deltaPhi I (σ (g i)) (g i) (fun j => Q j (g i)) i ≤ deltaPhi I (σ m) m (fun j => Q j m) i) →
        ∑ i, lam i * ((deltaPhi I (σ (g i)) (g i) (fun j => Q j (g i)) i : ℤ) : ℝ) ≤
          ∑ i, lam i * ∑ m, p i m * ((deltaPhi I (σ m) m (fun j => Q j m) i : ℤ) : ℝ)) ∧
      ∑ i, lam i * ∑ m, p i m * ((deltaPhi I (σ m) m (fun j => Q j m) i : ℤ) : ℝ) ≤
        -δ * Real.sqrt ((Phi B σ Q : ℤ) : ℝ) / (2 * (n : ℝ) ^ 2) := by sorry

end MultiwaySoS
