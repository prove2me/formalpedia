-- Prove2me | Theorems.Thm_FracPSG_Abstract_eq_24
-- name    : FracPSG.Abstract.eq_24
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T21:08:40.743041+00:00
-- url     : https://prove2.me/theorems/fe5e5449-ff20-47a7-ba94-5e57f1768084
-- title:
--   (24), proof of Theorem 5.2(i) — tail bound on the sum of Δₖ
-- statement:
--   Assume the hypotheses of Theorem 5.2: (H1)–(H4), $(z_n)$ bounded, $h$ constant on the cluster set $\Omega$ and with the KL property at each point of $\Omega$. Let $\bar z\in\Omega_0$ and suppose that $h(z_n)>h(\bar z)$ for all $n$ (Case 2 of the proof); put $r_n:=h(z_n)-h(\bar z)$. Then there are $\eta>0$, $\varphi\in\Phi_\eta$ and $n_0$ such that, for $n\ge n_0$, $h(z_n)<h(\bar z)+\eta$ and $\varphi'(r_n)\operatorname{dist}(0,\partial_L h(z_n))\ge1$ (this is (22)); and for every $\gamma>0$ with $\gamma\le\alpha_n\beta_n$ for all $n$ (for instance $\gamma=\underline\gamma$) and every $n\ge\max\{n_0,\bar\imath\}$,
--   $$\sum_{k=n}^{+\infty}\Delta_k\le\frac1{\gamma}\varphi(r_n)+\sum_{i=1}^{\bar\imath}\Delta_{n-i}+\sum_{k=n}^{+\infty}\varepsilon_k<+\infty. \qquad (24)$$
--
--   (24) is the finite-length estimate: it bounds the tail of $\sum\Delta_k$ by the desingularized value gap plus finitely many earlier terms and the tail of the errors.
--
--   **Formalization Note** The sum $\sum_{i=1}^{\bar\imath}$ is empty when $\bar\imath\le0$. The tail sums are `tsum`s over $k\ge0$ of $\Delta_{n+k}$ and $\varepsilon_{n+k}$, and summability of the $\Delta$ tail is part of the conclusion. Stating it for every lower bound $\gamma$ of $\alpha_n\beta_n$ is equivalent to stating it for $\underline\gamma$, since $\varphi\ge0$. Distances are encoded as for Lemma 2.3.
-- source:
--   Boţ, Dao, Li, Extrapolated Proximal Subgradient Algorithms for Nonconvex and Nonsmooth Fractional Programs, arXiv:2003.04124v2, p. 16, proof of Theorem 5.2(i), (22) and (24)

import Mathlib
import Definitions.Def_NonconvexSplitting_Shared_StandingAssumptions
import Definitions.Def_NonconvexSplitting_Shared_LimitingSubdiff
import Definitions.Def_NonconvexSplitting_ADMMKL_KLProperty
import Definitions.Def_FracPSG_Abstract_Basic

open Filter Topology

namespace FracPSG.Abstract

open NonconvexSplitting.Shared NonconvexSplitting.ADMMKL

/-- (24), proof of Theorem 5.2(i), Case 2 (Boţ–Dao–Li, arXiv:2003.04124v2, p. 16): under the
hypotheses of Theorem 5.2, let `z̄ ∈ Ω₀` with `h(zₙ) > h(z̄)` for all `n`, and `rₙ := h(zₙ) - h(z̄)`.
Then there are `η > 0`, `φ ∈ Φ_η` and `n₀` such that (22) holds for `n ≥ n₀`, and, for every
`γ > 0` with `γ ≤ αₙβₙ` for all `n` (e.g. `γ = γ̲`) and every `n ≥ max{n₀, ı̄}`,
`∑_{k ≥ n} Δ_k ≤ φ(rₙ)/γ + ∑_{i=1}^{ı̄} Δ_{n-i} + ∑_{k ≥ n} ε_k < +∞`. -/
theorem eq_24 {P : ℕ} {h : EuclideanSpace ℝ (Fin P) → EReal}
    {z : ℕ → EuclideanSpace ℝ (Fin P)} {α β ε : ℕ → ℝ} {Δ : ℤ → ℝ} {ilo ihi : ℤ}
    {lam : ℤ → ℝ}
    (hset : AbstractSetting h α β ε Δ ilo ihi lam)
    (hH1 : H1 h z α Δ) (hH2 : H2 h z β ε Δ ilo ihi lam) (hH3 : H3 h z) (hH4 : H4 α β ε)
    (hbdd : Bornology.IsBounded (Set.range z))
    (hconst : ∀ z₁ ∈ clusterSet z, ∀ z₂ ∈ clusterSet z, h z₁ = h z₂)
    (hKL : ∀ zbar ∈ clusterSet z, HasKLProperty h zbar) :
    ∀ zbar ∈ omega0 h z, (∀ n, h zbar < h (z n)) →
      ∃ η : ℝ, 0 < η ∧ ∃ φ : ℝ → ℝ, IsDesingularizer η φ ∧ ∃ n₀ : ℕ,
        (∀ n, n₀ ≤ n → h (z n) < h zbar + (η : EReal) ∧
          ∀ v ∈ LimitingSubdiff h (z n),
            1 ≤ deriv φ ((h (z n)).toReal - (h zbar).toReal) * ‖v‖) ∧
        ∀ γ : ℝ, 0 < γ → (∀ n, γ ≤ α n * β n) →
          ∀ n : ℕ, n₀ ≤ n → ihi ≤ (n : ℤ) →
            Summable (fun k : ℕ => Δ ((n + k : ℕ) : ℤ)) ∧
            ∑' k : ℕ, Δ ((n + k : ℕ) : ℤ) ≤
              φ ((h (z n)).toReal - (h zbar).toReal) / γ +
                ∑ i ∈ Finset.Icc (1 : ℤ) ihi, Δ ((n : ℤ) - i) +
                ∑' k : ℕ, ε (n + k) := by sorry

end FracPSG.Abstract
