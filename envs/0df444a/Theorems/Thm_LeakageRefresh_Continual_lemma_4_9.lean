-- Prove2me | Theorems.Thm_LeakageRefresh_Continual_lemma_4_9
-- name    : LeakageRefresh.Continual.lemma_4_9
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T23:11:40.709944+00:00
-- url     : https://prove2.me/theorems/7bf80742-2214-408b-98a4-42fdef5c366c
-- title:
--   Lemma 4.9 — cancellation of the consistency sign: $|\langle J,uv^T\rangle|\le\frac{N}{2q^2}\|u\|_2\|v\|_2$ and $|\langle J\cdot\mathrm{prob}_z^{>\beta},uv^T\rangle|\le\frac1{q\beta}$
-- statement:
--   Let $n\ge2$, $N=2^n$, $q=N-1$, and let $J$ be the sign table of Eq. (4.30) on $U_L^2\times U_R^2$. For arbitrary real functions $u$ on $U_L^2$ and $v$ on $U_R^2$,
--   $$\big|\langle J,u\,v^T\rangle\big|\le\frac{N}{2q^2}\|u\|_2\|v\|_2\le\frac1q\|u\|_2\|v\|_2. \tag{4.32}$$
--   Fix the leakage functions of a round, an answer $z$, an orthonormal expansion of $\mathrm{prob}_z$ and $\beta\in[q^{-1/3},1]$. For all $u:U_L^2\to\mathbb R$, $v:U_R^2\to\mathbb R$ with $\|u\|_2=\|v\|_2=1$,
--   $$\big|\langle J\cdot\mathrm{prob}_z^{>\beta},u\,v^T\rangle\big|\le\frac{1}{q\beta}, \tag{4.33}$$
--   where $J\cdot F$ is the entrywise product.
--
--   Differences from the source:
--   - encoding: the chain $|\langle J,uv^T\rangle|\le\frac{N}{2q^2}\|u\|\|v\|\le\frac1q\|u\|\|v\|$ → a conjunction of the two inequalities; reason: a chain of inequalities is the conjunction of its links
--   - encoding: a fixed formal incoming history and adversary tape (which fix the two leakage functions) → an arbitrary pair of leakage functions `lp : LeakPair n lam`; reason: every pair of leakage functions arises from some strategy, history and tape, and conversely
--   - reading: the truncation $\mathrm{prob}_z^{>\beta}$ of "an orthonormal expansion" of $\mathrm{prob}_z$ (Eq. (4.7)) → the statement holds for every orthonormal expansion `E : OrthoExpansion (probTable lp z)`; reason: the paper takes an arbitrary expansion and notes the truncation does not depend on it; quantifying over all expansions is that reading
-- source:
--   Dziembowski, Faust, Leakage-Resilient Computation via Matrix Refreshing, arXiv:2611.04876 (sha256 fdbb2454…), p. 35, Lemma 4.9

import Mathlib
import Definitions.Def_LeakageRefresh_Continual_Encoding
import Definitions.Def_LeakageRefresh_Continual_LeakageModel
import Definitions.Def_LeakageRefresh_Continual_Tables
import Definitions.Def_LeakageRefresh_Continual_OneRound

namespace LeakageRefresh.Continual

/-- **Lemma 4.9 (Cancellation of the consistency sign).** With `N = 2ⁿ`, `q = N − 1`:
(4.32) for all real `u` on `U_L²` and `v` on `U_R²`,
`|⟨J, u vᵀ⟩| ≤ N/(2q²) ‖u‖₂ ‖v‖₂ ≤ (1/q) ‖u‖₂ ‖v‖₂`;
(4.33) for fixed leakage functions, every answer `z`, every `β ∈ [q^{−1/3}, 1]`, every
orthonormal expansion of `prob_z` and all `u`, `v` with `‖u‖₂ = ‖v‖₂ = 1`,
`|⟨J · prob_z^{>β}, u vᵀ⟩| ≤ 1/(q β)`. -/
theorem lemma_4_9 (n : ℕ) (hn : 2 ≤ n) :
    (∀ (u : UL n × UL n → ℝ) (v : UR n × UR n → ℝ),
      |tableIp (signJ n) (outer u v)| ≤
          (2 : ℝ) ^ n / (2 * ((2 : ℝ) ^ n - 1) ^ 2) * l2 u * l2 v ∧
        (2 : ℝ) ^ n / (2 * ((2 : ℝ) ^ n - 1) ^ 2) * l2 u * l2 v ≤
          1 / ((2 : ℝ) ^ n - 1) * l2 u * l2 v) ∧
    (∀ (lam : ℕ) (lp : LeakPair n lam) (z : Answer lam) (β : ℝ),
      ((2 : ℝ) ^ n - 1) ^ (-(1 / 3 : ℝ)) ≤ β → β ≤ 1 →
      ∀ (E : OrthoExpansion (probTable lp z)) (u : UL n × UL n → ℝ) (v : UR n × UR n → ℝ),
        l2 u = 1 → l2 v = 1 →
        |tableIp (fun p q => signJ n p q * E.trunc β p q) (outer u v)| ≤
          1 / (((2 : ℝ) ^ n - 1) * β)) := by sorry

end LeakageRefresh.Continual
