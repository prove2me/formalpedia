-- Prove2me | Theorems.Thm_LeakageRefresh_Continual_eq_4_4
-- name    : LeakageRefresh.Continual.eq_4_4
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T23:11:19.3752+00:00
-- url     : https://prove2.me/theorems/2bf8c4cc-7365-4600-800a-7e62850af30e
-- title:
--   §4.2, Eq. (4.4) — the transcript law equals the independent-encoding experiment $\mathbb E_{\mu_s^{\otimes(T+1)}}\prod_i\mathrm{prob}_{i,h_{i-1},z_i}(X_{i-1},X_i)$
-- statement:
--   Let $n\ge2$, $T,\lambda\ge0$, fix a deterministic strategy and a secret $s$. For every complete history $h=(z_1,\dots,z_T)\in\mathcal Z^T$, with $h_{i-1}=(z_1,\dots,z_{i-1})$,
--   $$P_s^T(h)=\mathbb E_{(X_0,\dots,X_T)\leftarrow\mu_s^{\otimes(T+1)}}\Big[\prod_{i=1}^T\mathrm{prob}_{i,h_{i-1},z_i}(X_{i-1},X_i)\Big],$$
--   where $P_s^T$ is the law of the transcript of the real execution and $\mathrm{prob}_{i,h,z}$ is the leakage probability function of Definition 4.2. The exact experiment samples all states independently first and draws the answers afterward; it is the starting point of the hybrid argument.
--
--   Differences from the source:
--   - encoding: rounds $i\in\{1,\dots,T\}$ with incoming history $h\in\mathcal Z^{i-1}$ → `i : Fin T` is round $i+1$, with incoming history `Fin i → Answer lam`; reason: 0-based indexing of the same rounds and histories
--   - encoding: $\mathbb E_{(X_0,\dots,X_T)\leftarrow\mu_s^{\otimes(T+1)}}[\cdot]$ → $\sum_{X:\mathrm{Fin}(T+1)\to U_L\times U_R}\prod_k\mu_s(X_k)\cdot[\cdot]$; reason: expectation under a product of finite distributions
--   - encoding: $\mathrm{prob}_{i,h,z}$ defined on $\Omega_s\times\Omega_s$ → `ansProb` defined on all pairs of states, $0$ where no invertible matrix connects them; reason: only pairs in $\Omega_s\times\Omega_s$ carry weight in the sum
-- source:
--   Dziembowski, Faust, Leakage-Resilient Computation via Matrix Refreshing, arXiv:2611.04876 (sha256 fdbb2454…), p. 28, §4.2, Eq. (4.4)

import Mathlib
import Definitions.Def_LeakageRefresh_Continual_Encoding
import Definitions.Def_LeakageRefresh_Continual_LeakageModel
import Definitions.Def_LeakageRefresh_Continual_OneRound

namespace LeakageRefresh.Continual

/-- **§4.2, Eq. (4.4) (exact experiment with independent encodings).** For every complete
history `h = (z₁, …, z_T)`, `P_sᵀ(h) = E_{(X₀,…,X_T) ←$ µₛ^{⊗(T+1)}}[∏ᵢ prob_{i,h_{i−1},zᵢ}(X_{i−1}, Xᵢ)]`.
Round `i : Fin T` is the paper's round `i + 1`, with incoming history the first `i` answers of
`h`, old state `X i.castSucc` and new state `X i.succ`. -/
theorem eq_4_4 (n T lam : ℕ) (hn : 2 ≤ n) (σ : Strategy n T lam) (s : ZMod 2)
    (h : Fin T → Answer lam) :
    transcriptLaw σ s h =
      ∑ X : Fin (T + 1) → State n, (∏ k, mu n s (X k)) *
        ∏ i : Fin T, ansProb (σ i (fun j : Fin i => h (Fin.castLE i.isLt.le j))) (h i)
          (X i.castSucc) (X i.succ) := by sorry

end LeakageRefresh.Continual
