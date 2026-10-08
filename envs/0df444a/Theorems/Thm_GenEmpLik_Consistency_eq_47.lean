-- Prove2me | Theorems.Thm_GenEmpLik_Consistency_eq_47
-- name    : GenEmpLik.Consistency.eq_47
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T08:53:22.571562+00:00
-- url     : https://prove2.me/theorems/8b2b31d0-50a5-41c3-9e29-856577bf9c7f
-- title:
--   (47) — Hölder bound on the deviation of a reweighted mean from E_{P₀}[ℓ]
-- statement:
--   Let $\epsilon>0$ and set $q=\min\{2,1+\epsilon\}$, $r=\max\{2,1+1/\epsilon\}$ (conjugate exponents: $1/r+1/q=1$). Let $n\ge1$, let $z=(z_1,\dots,z_n)$ be real numbers (the losses $\ell(x;\xi_i)$), $m\in\mathbb R$ (standing for $E_{P_0}[\ell(x;\xi)]$), and let $w$ be a weight vector in the ball $\{w\ge0:\sum_i w_i=1,\ \sum_i f(nw_i)\le\rho\}$, i.e. a distribution $P\ll\widehat P_n$ with likelihood ratio $L(\xi_i)=nw_i$. Writing $E_{\widehat P_n}[g]=\frac1n\sum_i g_i$ and $\bar z=\frac1n\sum_i z_i$,
--
--   $$
--   \Big|\sum_{i=1}^n w_i z_i-m\Big|
--   \ \le\ \frac1n\sum_{i=1}^n|nw_i-1|\,|z_i|+|\bar z-m|
--   \ \le\ \Big(\frac1n\sum_{i=1}^n|nw_i-1|^{r}\Big)^{1/r}\Big(\frac1n\sum_{i=1}^n|z_i|^{q}\Big)^{1/q}+|\bar z-m| .
--   $$
--
--   In the paper's notation this is $|E_P[\ell]-E_{P_0}[\ell]|\le E_{\widehat P_n}[|L-1||\ell|]+|E_{\widehat P_n}[\ell]-E_{P_0}[\ell]|\le E_{\widehat P_n}[|L-1|^r]^{1/r}E_{\widehat P_n}[|\ell|^q]^{1/q}+|E_{\widehat P_n}[\ell]-E_{P_0}[\ell]|$; taking suprema over the ball gives the printed form of (47). It splits the robust deviation into a reweighting term, controlled by Lemma 13 and Assumption E, and the ordinary empirical deviation, controlled by the Glivenko–Cantelli property.
--
--   **Formalization Note** The paper's exponent $p$ is called $r$ here to avoid a clash with the weights. The middle term uses $|\ell|$: the page prints $|L(\xi)-1|\,\ell(x;\xi)$, a typo (the bound fails for signed $\ell$ otherwise). The statement is per distribution; the printed version takes the supremum over the ball on both sides.
-- source:
--   Duchi, Glynn & Namkoong, Statistics of Robust Optimization: A Generalized Empirical Likelihood Approach, arXiv:1610.03425v3, p. 46, App. E.1, proof of Theorem 7, (47)

import Mathlib
import Definitions.Def_PhiDivRobust_Counterpart_uncertaintySet
import Definitions.Def_VarianceRegularization_Expansion_empMean

namespace GenEmpLik.Consistency

/-- Inequality (47) (arXiv:1610.03425v3, App. E.1, p. 46), for one distribution `P` of the
ball `𝒫_{n,ρ}`. Let `ε > 0`, `q = min{2, 1 + ε}`, `r = max{2, 1 + 1/ε}` (the paper's `p`), let
`z = (ℓ(x; ξ₁), …, ℓ(x; ξₙ))` and `m` a real number (standing for `E_{P₀}[ℓ(x; ξ)]`). For every
weight vector `w` in the ball, with likelihood ratio `L(ξᵢ) = n wᵢ`,
`|E_P[ℓ] − m| ≤ E_{P̂n}[|L − 1| |ℓ|] + |E_{P̂n}[ℓ] − m|
  ≤ E_{P̂n}[|L − 1|^r]^{1/r} E_{P̂n}[|ℓ|^q]^{1/q} + |E_{P̂n}[ℓ] − m|`. -/
theorem eq_47 (f : ℝ → EReal) (ρ ε : ℝ) (hε : 0 < ε) (n : ℕ) (hn : 0 < n)
    (z : Fin n → ℝ) (m : ℝ)
    (w : Fin n → ℝ) (hw : w ∈ PhiDivRobust.Counterpart.probUncertaintySet f
      (fun _ : Fin n => (1 : ℝ) / n) (ρ / n)) :
    |∑ i, w i * z i - m| ≤
        (1 / (n : ℝ)) * ∑ i, |(n : ℝ) * w i - 1| * |z i|
          + |VarianceRegularization.Expansion.empMean z - m| ∧
      (1 / (n : ℝ)) * ∑ i, |(n : ℝ) * w i - 1| * |z i|
          + |VarianceRegularization.Expansion.empMean z - m| ≤
        ((1 / (n : ℝ)) * ∑ i, |(n : ℝ) * w i - 1| ^ max 2 (1 + 1 / ε)) ^ (1 / max 2 (1 + 1 / ε))
          * ((1 / (n : ℝ)) * ∑ i, |z i| ^ min 2 (1 + ε)) ^ (1 / min 2 (1 + ε))
          + |VarianceRegularization.Expansion.empMean z - m| := by sorry

end GenEmpLik.Consistency
