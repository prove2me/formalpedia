-- Prove2me | Theorems.Thm_KWPurify_Rate_prop_4_2_block
-- name    : KWPurify.Rate.prop_4_2_block
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T17:29:57.242795+00:00
-- url     : https://prove2.me/theorems/979fb4af-dd5a-4ad6-992f-14f2b91ed7bb
-- title:
--   Proposition 4.2 (corrected) — per-block fidelity $\operatorname{tr}(\sigma^{\otimes M}\hat Q_{2s*}(\rho_s(\beta))) = f_{\mathrm{all}}(M,\beta,s)$
-- statement:
--   Let $\beta > 0$, $q = e^{-2\beta}$, $n = 2s \in \mathbb N$ and $M \in \mathbb N$; let $\sigma_0 = |\psi\rangle\langle\psi|$ with $\psi = (1,0)$. Let $\hat Q_{n*}$ be the optimal map from $n$ to $M$ qubits: the partial trace over the first $n-M$ tensor factors if $M \le n$, and the optimal cloner $\theta\mapsto\frac{n+1}{M+1}S_M(\theta\otimes\mathbb 1^{\otimes(M-n)})S_M$ if $M > n$. Then
--   $$\operatorname{tr}\big(\sigma_0^{\otimes M}\,\hat Q_{n*}(\rho_s(\beta))\big) = f_{\mathrm{all}}(M,\beta,s) = \begin{cases} \dfrac{n+1}{M+1}\,\dfrac{1-q}{1-q^{n+1}} & M > n,\\[2mm] \dfrac{1-q}{1-q^{n+1}}\dbinom{n}{M}^{-1}\displaystyle\sum_{K=M}^{n}\binom{K}{M} q^{\,n-K} & M \le n.\end{cases}$$
--
--   This is the content of Proposition 4.2 for one spin block; summed against the weights $w_N(s)$ it gives the all-qubit fidelity of the optimal purifier (eq. (31)).
--
--   **Formalization Note** Corrected statement. As printed, (32) has its case labels swapped (the cloner branch is the case $M > 2s$, as the computation on p. 14 says, and the printed $M > 2s$ branch would divide by $\binom{2s}{M} = 0$), and its exponent $e^{2\beta(K-s)}$ omits the factor $e^{-2\beta s}$ of the normalization of $\rho_s(\beta)$ (the printed value at $M = 0$ exceeds $1$). The correct exponent is $e^{2\beta(K-2s)} = q^{n-K}$. The purifier $T^{\mathrm{opt}}$ itself is not defined; the statement is the per-block computation.
-- source:
--   Keyl & Werner, The Rate of Optimal Purification procedures, arXiv:quant-ph/9910124v1, pp. 14–15, computation of f_all and Proposition 4.2, eq. (32) (corrected)

import Mathlib
import Definitions.Def_QAlgorithms_Defs_GradientMethods
import Definitions.Def_KWPurify_Rate_Blocks

namespace KWPurify.Rate
theorem prop_4_2_block (β : ℝ) (hβ : 0 < β) (n M : ℕ) :
    (QAlgorithms.piKron M psiDensity * optimalBlockMap n M (boseState β n)).trace.re =
      fAll M β n := by sorry
end KWPurify.Rate
