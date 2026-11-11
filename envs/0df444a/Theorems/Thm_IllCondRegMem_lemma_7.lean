-- Prove2me | Theorems.Thm_IllCondRegMem_lemma_7
-- name    : IllCondRegMem.lemma_7
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T09:56:24.294757+00:00
-- url     : https://prove2.me/theorems/a5291dbf-bd3b-41e7-a896-0683bf58d127
-- title:
--   Lemma 7 — online subspace generation: $\mathbb P\{P_{G_k}P_{V_k}P_{G_k}\not\succeq\rho P_{G_k}\}\le Cd\rho k^{1/(\ell-1)}+e^{-d}$
-- statement:
--   Consider the online column generation process: for each $i\in[k]$ a unit vector $g_i\notin\mathrm{Span}(g_1,\dots,g_{i-1})$ is selected, possibly depending on $z_1,\dots,z_{\ell(i-1)}$, then $z_{\ell(i-1)+1},\dots,z_{\ell i}$ are drawn i.i.d. $\mathcal N(0,I_d)$; $G_j=\mathrm{Span}(g_1,\dots,g_j)$ and $V_j=\mathrm{Span}(z_1,\dots,z_{\ell j})$.
--
--   1. There is a universal constant $C>0$ such that for all $\ell\ge3$, $k\le d/(2\ell)$, $\rho\ge0$ and every strategy,
--   $$
--   \mathbb P\{P_{G_k}P_{V_k}P_{G_k}\not\succeq\rho P_{G_k}\}\le Cd\rho\,k^{1/(\ell-1)}+e^{-d}.
--   $$
--   2. For $\ell=4$ there is a universal constant $C>0$ such that for all $k\le d/8$, $\rho\ge0$ and every strategy,
--   $$
--   \mathbb P\{\exists j\in[k]:P_{G_j}P_{V_j}P_{G_j}\not\succeq\rho P_{G_j}\}\le C(d\rho)^{3/2}k^{3/2}+e^{-d}.
--   $$
--   Adaptively chosen directions cannot be nearly orthogonal to the span of fresh Gaussians, which keeps the masking subspaces of the adversary informative (eq. (5)).
--
--   **Formalization Note** Strategies are measurable and non-anticipating; $z\sim\mathcal N(0,I_d)^{\otimes\ell k}$.
--
--   Differences from the source:
--   - reading: "some C_ℓ > 0 dependent only on ℓ and universal constant c > 0" with the display using C → one universal C for all ℓ ≥ 3; reason: the stronger reading; the proof (pp.41–42) gives a bound uniform in ℓ ≥ 3
--   - reading: ∃ℓ ∈ [k] in the second claim (ℓ already fixed to 4) → ∃ j ∈ [k] = {1, …, k}; reason: the proof (p.44) writes j ∈ [k]
--   - encoding: selection process; k ≤ d/(2ℓ); ⋡ → measurable non-anticipating ColumnStrategy; 2ℓk ≤ d; NotDominates (some x ∈ G with ⟨x, P_V x⟩ < ρ‖x‖²); reason: Lean representation; same events
-- source:
--   M. Blanchard, D. Hansen, A. Jayant, V. Sharan, Polynomial Memory-Sample Separations in Non-i.i.d. Ill-Conditioned Regression, STOC 2027 submission (held version, sha256 6369d09f…), Lemma 7, p.9 (PDF p.10); restated p.40 (PDF p.41)

import Mathlib
import Definitions.Def_IllCondRegMem_ColumnStrategy

open MeasureTheory ProbabilityTheory

namespace IllCondRegMem

/-- **Lemma 7 (Online Subspace Generation).**
Blanchard, Hansen, Jayant, Sharan, *Polynomial Memory-Sample Separations in Non-i.i.d.
Ill-Conditioned Regression*, STOC 2027 submission (held version, sha256 6369d09f…), Lemma 7,
p.9 (restated p.40): "Fix ℓ ≥ 3, k ≤ d/(2ℓ) and some ρ ≥ 0. Consider the following column
generation process. For each i ∈ [k], select a unit vector g_i ∉ Span(g₁, …, g_{i−1}) possibly
dependent on z₁, …, z_{ℓ(i−1)}; then draw ℓ independent Gaussians z_{ℓ(i−1)+1}, …, z_{ℓi}
iid∼ N(0, I_d). Let G_k := Span(g₁, …, g_k) and V_k := Span(z₁, …, z_{ℓk}). Then, there is some
C_ℓ > 0 dependent only on ℓ and universal constant c > 0 such that
P{P_{G_k} P_{V_k} P_{G_k} ⋡ ρP_{G_k}} ≤ Cdρk^{1/(ℓ−1)} + e^{−d}. Moreover, when ℓ = 4, there is a
universal constant C > 0 such that P{∃ℓ ∈ [k] : P_{G_ℓ} P_{V_ℓ} P_{G_ℓ} ⋡ ρP_{G_ℓ}} ≤
C(dρ)^{3/2}k^{3/2} + e^{−d}."

**Formalization Note.** First claim: one constant `C` for all `ℓ ≥ 3` (the proof, pp.41–42,
gives a bound uniform in `ℓ ≥ 3`; this is the stronger reading of the display, which uses `C`).
Second claim: the bound variable of "∃ℓ ∈ [k]" is read as `j ∈ [k] = {1, …, k}`, as in the proof
(p.44), with `ℓ = 4`. `k ≤ d/(2ℓ)` is `2ℓk ≤ d`. The process is a `ColumnStrategy`;
`z ∼ N(0, I_d)^{⊗ℓk}`; `P_G P_V P_G ⋡ ρP_G` is `NotDominates G V ρ`. -/
theorem lemma_7 :
    (∃ C : ℝ, 0 < C ∧ ∀ (d ℓ k : ℕ) (ρ : ℝ) (S : ColumnStrategy d ℓ k),
      3 ≤ ℓ → 2 * ℓ * k ≤ d → 0 ≤ ρ →
      (Measure.pi fun _ : Fin (ℓ * k) => stdGaussian (Vec d))
          {z | NotDominates (colSpanG S z k) (colSpanV z k) ρ} ≤
        ENNReal.ofReal (C * d * ρ * (k : ℝ) ^ (1 / ((ℓ : ℝ) - 1)) + Real.exp (-(d : ℝ)))) ∧
    (∃ C : ℝ, 0 < C ∧ ∀ (d k : ℕ) (ρ : ℝ) (S : ColumnStrategy d 4 k),
      2 * 4 * k ≤ d → 0 ≤ ρ →
      (Measure.pi fun _ : Fin (4 * k) => stdGaussian (Vec d))
          {z | ∃ j : ℕ, 1 ≤ j ∧ j ≤ k ∧ NotDominates (colSpanG S z j) (colSpanV z j) ρ} ≤
        ENNReal.ofReal (C * ((d : ℝ) * ρ) ^ ((3 : ℝ) / 2) * (k : ℝ) ^ ((3 : ℝ) / 2) +
          Real.exp (-(d : ℝ)))) := by sorry

end IllCondRegMem
