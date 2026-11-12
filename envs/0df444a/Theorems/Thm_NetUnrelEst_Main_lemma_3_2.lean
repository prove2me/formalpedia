-- Prove2me | Theorems.Thm_NetUnrelEst_Main_lemma_3_2
-- name    : NetUnrelEst.Main.lemma_3_2
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T07:15:14.007487+00:00
-- url     : https://prove2.me/theorems/0a135480-cdd1-41dc-bb3b-a475d74d7044
-- title:
--   Lemma 3.2 — the exponent shift z_{1−d} ≤ 2u exp(B_β dλ), and z_{1−d} ≤ C_{β,γ}u for dλ ≤ γ
-- statement:
--   For every $\beta>0$ there are constants $B_\beta\ge2$ and $n_\beta$ such that every connected graph with positive capacities ($0<p_e<1$), $n\ge n_\beta$ vertices and unreliability $u\le n^{-\beta}$ satisfies
--   $$z_{1-d}\le 2u\exp(B_\beta d\lambda)\qquad\text{whenever}\qquad 0\le d\lambda\le\frac{\log(1/u)}{2B_\beta}.\tag{21}$$
--   Moreover, for every $\gamma>0$ there are $C_{\beta,\gamma}$ and a size threshold depending only on $\beta,\gamma$ such that, for larger $n$,
--   $$z_{1-d}\le C_{\beta,\gamma}\,u\qquad\text{whenever } d\ge0,\ d\lambda\le\gamma.\tag{22}$$
--   Here $z_{1-d}=\sum_C a_C^{1-d}$ is the cut sum after replacing each $p_e$ by $p_e^{1-d}$.
--
--   Raising failure probabilities increases the cut sum; the lemma says that for polynomially small $u$ a shift of order $1/\lambda$ in the exponent costs only a constant factor. It is used at $d=2s^*$ for Theorem 2.3 and with $d$ proportional to elapsed time in Theorem 3.5.
--
--   **Formalization Note.** Both clauses are stated with their constants quantified before the graph; (22) has its own constant and threshold for every $\gamma>0$.
--
--   Differences from the source:
--   - generalization: every connected positive-capacity graph → every connected multigraph on Fin n (self-loops and parallel edges allowed) with 0 < p_e < 1; reason: loops cross no cut and parallel edges combine into one edge of summed capacity, so u, λ and z_{1−d} are those of the simple graph; a graph is one instance
--   - encoding: 'for sufficiently large n depending only on β, γ' and the constant C_{β,γ} in (22) → ∀ γ > 0, ∃ C, ∃ n', for every graph with n ≥ n'; reason: the meaning of the phrase; C and n' depend only on β and γ
-- source:
--   Sun, Near-Linear Estimation of Network Unreliability, STOC 2027 submission, doi:10.5281/zenodo.23913531 (PDF sha256 eee2585a…), p. 16, Lemma 3.2

import Mathlib
import Definitions.Def_NetUnrelDesign_Main_Model
import Definitions.Def_NetUnrelEst_Main_CutSums

open scoped BigOperators ENNReal

open NetUnrelDesign.Main

namespace NetUnrelEst.Main

/-- **Lemma 3.2.** For every `β > 0` there are `B_β ≥ 2` and `n_β` such that every connected
positive-capacity graph with `n ≥ n_β` and `u ≤ n^{−β}` satisfies `z_{1−d} ≤ 2u exp(B_β dλ)`
whenever `0 ≤ dλ ≤ log(1/u)/(2B_β)` (21); and for every `γ > 0` there are `C_{β,γ}` and a size
threshold such that `z_{1−d} ≤ C_{β,γ} u` whenever `d ≥ 0`, `dλ ≤ γ` (22). Sun 2027, p. 16,
Lemma 3.2. -/
theorem lemma_3_2 (β : ℝ) (hβ : 0 < β) :
    (∃ B : ℝ, 2 ≤ B ∧ ∃ nβ : ℕ, ∀ {n m : ℕ} (ends : Ends n m), nβ ≤ n → IsConnectedGraph ends →
      ∀ p : Fin m → ℝ, (∀ e, 0 < p e ∧ p e < 1) → unrel ends p ≤ (n : ℝ) ^ (-β) →
        ∀ d : ℝ, 0 ≤ d * lam ends p → d * lam ends p ≤ Real.log (1 / unrel ends p) / (2 * B) →
          zTheta ends p (1 - d) ≤ 2 * unrel ends p * Real.exp (B * d * lam ends p)) ∧
    (∀ γ : ℝ, 0 < γ → ∃ C : ℝ, ∃ n' : ℕ, ∀ {n m : ℕ} (ends : Ends n m), n' ≤ n →
      IsConnectedGraph ends → ∀ p : Fin m → ℝ, (∀ e, 0 < p e ∧ p e < 1) →
        unrel ends p ≤ (n : ℝ) ^ (-β) → ∀ d : ℝ, 0 ≤ d → d * lam ends p ≤ γ →
          zTheta ends p (1 - d) ≤ C * unrel ends p) := by sorry

end NetUnrelEst.Main
