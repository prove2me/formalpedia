-- Prove2me | Theorems.Thm_MaxCutMatrix2027_Upper_Supplement_max2csp_sampling_residual
-- name    : MaxCutMatrix2027.Upper.Supplement.max2csp_sampling_residual
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T18:13:29.251082+00:00
-- url     : https://prove2.me/theorems/518afbeb-bd25-40cf-a5a8-0539960d7353
-- title:
--   Lemma A.3 — Sampling the MAX-2CSP residual
-- statement:
--   Fix a MAX-2CSP instance $F$ on $n$ variables, a real $1\le s\le n$ and $0<\tau\le1$. Let $M$ be the symmetric $2n\times2n$ matrix of p.42, $L=\sum_{|\theta_j|>\tau n}\theta_ju_ju_j^T$ its retained spectral part and $R=M-L$. Include each variable independently with probability $s/n$ and let $P$ be the diagonal matrix carrying the selector $\xi_i$ at both coordinates $(i,0),(i,1)$. There is an absolute constant $C_{\mathrm{res}}>0$ (independent of $n,F,s,\tau$) such that
--   $$\frac1{s^2}\,\mathbb E\Bigl[\sup_{z\in\mathcal X}|z^TPRPz|\Bigr]\le C_{\mathrm{res}}\Bigl(\tau+\frac1{\tau s}+\frac1{\sqrt s}\Bigr),$$
--   where $\mathcal X=\{z\in[0,1]^{[n]\times\{0,1\}}:z_{i,0}+z_{i,1}=1\}$.
--
--   The supremum ranges over the whole fractional set; $R$ need not vanish on same-variable blocks. This controls the cost of discarding $R$ in the sample.
--
--   Differences from the source:
--   - encoding: vertices (variables) labelled by [n] → Fin n = {0,…,n−1}; reason: relabeling is bijective
--   - encoding: independent Bernoulli(s/n) selectors → the exact finite Bernoulli-subset expectation sampleAverage (s/n); reason: the subset weights are exactly the independent-selector law
-- source:
--   Songhua He, STOC 2027 submission #351 (October 2026), Lemma A.3, p.43 (PDF p.43); https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/351.pdf; PDF SHA-256 b38cd84079663d9e2eb7375d7bf1572d5dc7c2157cfaf90e175fd371a9503631

import Definitions.Def_MaxCutMatrix2027_Upper_Supplement_CSP
import Definitions.Def_MaxCutMatrix2027_Upper_MatrixModel
set_option autoImplicit false

namespace MaxCutMatrix2027.Upper.Supplement

/-- Lemma A.3, p.43, with the standing hypotheses of pp.42–43 (`1 ≤ s ≤ n`, `0 < τ ≤ 1`,
independent Bernoulli(`s/n`) selectors shared by both labels of a variable). -/
theorem max2csp_sampling_residual :
    ∃ C_res : ℝ, 0 < C_res ∧ ∀ (n : ℕ) (F : CSPInstance n) (s τ : ℝ),
      1 ≤ s → s ≤ n → 0 < τ → τ ≤ 1 →
      sampleAverage (s / n) (fun Q => cspAbsSup (cspRestrict Q (cspResidual F τ))) / s ^ 2 ≤
        C_res * (τ + 1 / (τ * s) + 1 / Real.sqrt s) := by sorry

end MaxCutMatrix2027.Upper.Supplement
