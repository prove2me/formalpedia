-- Prove2me | Theorems.Thm_MultiNashRepair_lemma_5_5
-- name    : MultiNashRepair.lemma_5_5
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T22:33:43.798774+00:00
-- url     : https://prove2.me/theorems/f080934a-1be5-4ef6-a64e-0da3155f17c3
-- title:
--   Lemma 5.5 — the legal tilted repair: $\gamma$ a probability vector with $\gamma_i<3/m$, $\gamma_i\le3\lambda_i$, nonnegative budgets, invariant preserved
-- statement:
--   Fix admissible controls for $\sigma$, $m\ge m_0$, a mixed profile $x$ of a game with payoffs in $[0,1]$, and memory $h_i\ge0$ with $H=\sum_ih_i\le L_0$ and $v_i=mh_i-H\le R_0H$. Let the probability vector $\lambda$ and mixed deviations $b_i$ satisfy (5.11) at $\mu=S_u(H)-\varsigma-d$ and the floor condition $r+Q\tau\le R_0$ (5.26), where $\pi_i=m\lambda_i$, $r=\max_i\pi_i-1$, $\tau=\sum_i\lambda_iv_i$. Define
--   $$Z_0=G_0-Q\tau,\qquad\chi_i=\pi_i\frac{G_0-Qv_i}{Z_0},\qquad\gamma_i=\frac{\chi_i}{m}\qquad(5.27).$$
--   Then
--   1. $\gamma$ is a probability vector with $\gamma_i<3/m$ and $\gamma_i\le3\lambda_i$, rational when $\lambda$ and $h$ are;
--   2. the reverse allocation $\delta_i=\frac{\beta}{m}(G_0-Qv_i-\chi_i)$ is nonnegative, has total mass $1-\rho$, and equals $D/m-\beta\gamma_i-\nu h_i$ with $D=\beta(G_0+QH)$;
--   3. the memory update $h^+=c(h+t\gamma)$, $H^+=c(H+t)$ preserves the invariant $h^+\ge0$, $H^+=\sum_ih^+_i\le L_0$, $mh^+_i-H^+\le R_0H^+$, and so does scaling by any $0<P\le1$ (descent);
--   4. $\sum_{i\ne j}\gamma_i\,d_{i,b_i}(x[j\leftarrow y_j])<9/m$ for every $j$ and mixed $y_j$ (5.59).
--
--   Differences from the source:
--   - generalization: a nonterminal state with a failed LP whose dual law satisfies (5.11) and (5.26) → any probability vector $\lambda$ and mixed deviations $b$ with (5.11), (5.26) and the memory bounds; nonterminality dropped; reason: the proof uses only these; contains the paper's case
--   - generalization: the lemma's conclusions → also descent scaling (p.29) and the fresh column bound (5.59), derived in the proof and in Lemma 5.12 from this lemma; reason: both follow from the lemma's bounds (p.29, p.42); the item contains the lemma
--   - encoding: $\gamma$ is a rational probability vector → rational whenever $\lambda$ and $h$ are rational; reason: in the paper $\lambda$ comes from a rational dual and $h$ is rational by (I1); the controls are rational
--   - generalization: game with rational payoffs in $[0,1]$ → any real game with payoffs in $[0,1]$ (`BoundedGame`); reason: the proof uses only $0\le u_i\le1$; contains the paper's rational games
-- source:
--   J. Tang, S. Ding, C. Fang, Breaking the One-Player Extension Barrier: History-Aware Repair for Multiplayer Approximate Nash Equilibria, arXiv:2611.06076 (preprint; held version, sha256 34b911ed…5c14), Lemma 5.5, (5.27), p.28; (5.26), p.28; proof, (5.28), p.29; (5.59), p.42

import Mathlib
import Definitions.Def_NashAmplification_Filtering_Model
import Definitions.Def_MultiNashRepair_Controls
import Definitions.Def_MultiNashRepair_Regret

open NashAmplification.Filtering (Mixed Utility Tuple BoundedGame)
open Finset

namespace MultiNashRepair

/-- **Lemma 5.5 (Legal Tilted Repair)** (Tang, Ding, Fang, arXiv:2611.06076, Lemma 5.5, (5.27),
p.28; (5.26), (5.28), (5.59), pp.28–29, 42).

Fix admissible controls, `m ≥ m0`, a mixed profile `x` of an `m`-player game with payoffs in
`[0,1]`, and memory `h_i ≥ 0` with `H = Σ_i h_i ≤ L0` and `v_i = m h_i − H ≤ R0 H`. Let the dual
law `λ` (a probability vector) with mixed deviations `b_i` satisfy (5.11) at the margin
`µ = S_u(H) − ς − d` and the floor condition (5.26) `r + Q τ ≤ R0`, where `π_i = m λ_i`,
`r = max_i π_i − 1`, `τ = Σ_i λ_i v_i`. Define `Z0 = G0 − Qτ`, `χ_i = π_i (G0 − Q v_i)/Z0`,
`γ_i = χ_i/m` (5.27). Then:
- `γ` is a probability vector with `γ_i < 3/m` and `γ_i ≤ 3λ_i`, rational when `λ` and `h` are;
- the reverse allocation `δ_i = (β/m)(G0 − Q v_i − χ_i)` is nonnegative, has total mass
  `1 − ρ`, and equals `D/m − βγ_i − νh_i` with `D = β(G0 + QH)`;
- the exact memory update (5.23) `h⁺ = c(h + tγ)`, `H⁺ = c(H + t)` preserves the maintained
  invariant `h⁺ ≥ 0`, `H⁺ ≤ L0`, `m h⁺_i − H⁺ ≤ R0 H⁺`, and so does descent scaling by any
  `0 < P ≤ 1` (p.29);
- the new generation's column bound (5.59): `Σ_{i≠j} γ_i d_{i,b_i}(x[j ← y_j]) < 9/m` for every
  `j` and mixed `y_j`.

**Formalization Note.** The hypotheses are those the proof uses; "nonterminal state" is not
needed and is dropped. Controls are `ctrl.knobs` (`c, t, ρ, β, ν, R0, G0, Q, L0` at `(f0, u)`). -/
theorem lemma_5_5 {σ : ℚ} (ctrl : Controls σ) {m : ℕ} {n : Fin m → ℕ} (hm : ctrl.m0 ≤ m)
    (hn : ∀ i, 0 < n i) (u : Utility n) (hu : BoundedGame u) (x : Mixed n)
    (hx : AGT.IsMixedProfile x) (lam' : Fin m → ℝ) (b : Mixed n) (hlam : AGT.IsLottery lam')
    (hb : AGT.IsMixedProfile b) (h : Fin m → ℝ) (hh0 : ∀ i, 0 ≤ h i)
    (hL0 : ∑ i, h i ≤ ctrl.knobs.L0)
    (hv : ∀ i, (m : ℝ) * h i - ∑ j, h j ≤ ctrl.knobs.R0 * ∑ j, h j)
    (h511 : ∀ (j : Fin m) (y : Fin (n j) → ℝ), AGT.IsLottery y →
      ∑ i, lam' i * deficitMix u (Function.update x j y) i (b i) <
        (scaled u x + ctrl.mu (scaled u x) (∑ i, h i)) / m)
    (h526 : (⨆ i, (m : ℝ) * lam' i) - 1 +
      ctrl.knobs.Q * ∑ i, lam' i * ((m : ℝ) * h i - ∑ j, h j) ≤ ctrl.knobs.R0) :
    let k := ctrl.knobs
    let H := ∑ i, h i
    let v : Fin m → ℝ := fun i => (m : ℝ) * h i - H
    let τ := ∑ i, lam' i * v i
    let γ : Fin m → ℝ := fun i => lam' i * (k.G0 - k.Q * v i) / (k.G0 - k.Q * τ)
    let δ : Fin m → ℝ := fun i => k.beta / m * (k.G0 - k.Q * v i - m * γ i)
    let h' : Fin m → ℝ := k.c • (h + k.t • γ)
    let H' := k.c * (H + k.t)
    (AGT.IsLottery γ ∧ (∀ i, γ i < 3 / m) ∧ (∀ i, γ i ≤ 3 * lam' i) ∧
      ((∀ i, IsRat (lam' i)) → (∀ i, IsRat (h i)) → ∀ i, IsRat (γ i))) ∧
    ((∀ i, 0 ≤ δ i) ∧ ∑ i, δ i = 1 - k.rho ∧
      ∀ i, δ i = k.Dsh H / m - k.beta * γ i - k.nu * h i) ∧
    ((∀ i, 0 ≤ h' i) ∧ ∑ i, h' i = H' ∧ H' ≤ k.L0 ∧ ∀ i, (m : ℝ) * h' i - H' ≤ k.R0 * H') ∧
    (∀ P : ℝ, 0 < P → P ≤ 1 →
      (∀ i, 0 ≤ P * h i) ∧ P * H ≤ k.L0 ∧ ∀ i, (m : ℝ) * (P * h i) - P * H ≤ k.R0 * (P * H)) ∧
    (∀ (j : Fin m) (y : Fin (n j) → ℝ), AGT.IsLottery y →
      ∑ i ∈ univ.erase j, γ i * deficitMix u (Function.update x j y) i (b i) < 9 / m) := by sorry

end MultiNashRepair
