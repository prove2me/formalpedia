-- Prove2me | Theorems.Thm_FractionalCalc_laplace_rlDeriv
-- name    : FractionalCalc.laplace_rlDeriv
-- status  : Open
-- author  : @LG
-- created : 2026-11-20T16:40:46.131236+00:00
-- url     : https://prove2.me/theorems/d66699bd-fff8-43d5-8e0c-1c1732eb1e1e
-- title:
--   Laplace transform of the Riemann–Liouville fractional derivative (Eq. 21)
-- statement:
--   Let $\nu>0$, $n=\lfloor\nu\rfloor+1$, and $g=I_{0+}^{\,n-\nu}f$. Suppose $f$ is continuous on $[0,\infty)$ and of exponential order $\alpha$, that each $g^{(k)}$ ($0\le k<n$) has a finite right limit $g^{(k)}(0+)=L_k$ at $0$, and that $D_{0+}^{\nu}f$ is of exponential order $\alpha$. For $\operatorname{Re}s>\max(\alpha,0)$,
--   $$\mathcal L\big[D_{0+}^{\nu}f\big](s)=s^{\nu}\mathcal L[f](s)-\sum_{k=0}^{n-1}s^{\,n-k-1}\,g^{(k)}(0+).$$
--   This is Eq. (21) of the source; the initial terms involve the auxiliary function $g=I^{n-\nu}f$, not $f$ itself.
--
--   **Formalization Note** The right limits $g^{(k)}(0+)$ are given as a family $L_k$ with explicit `Tendsto` hypotheses at $0$ within $(0,\infty)$. Contrast with the Caputo formula (Eq. 24), whose initial terms are $f^{(k)}(0+)$.
-- source:
--   F. G. Rodrigues & E. C. de Oliveira, Rev. Bras. Ens. Fís. 37(3), 3305 (2015), https://doi.org/10.1590/S1806-11173731842, §4, Eq. (21), $g^{(k)}(0+)=\lim_{t\to0+}D^k I_{0+}^{n-\nu}f(t)$.

import Mathlib
import Definitions.Def_FractionalCalc_rlIntegral
import Definitions.Def_FractionalCalc_rlDeriv
import Definitions.Def_QueueingFundamentals_Transient_laplace
open MeasureTheory Set Classical QueueingFundamentals.Transient Filter

namespace FractionalCalc
theorem laplace_rlDeriv (ν α : ℝ) (f : ℝ → ℝ) (s : ℂ)
    (hν : 0 < ν) (n : ℕ) (hn : n = Nat.floor ν + 1)
    (hf : ContinuousOn f (Ici 0))
    (hexp : ∃ M T : ℝ, 0 < M ∧ 0 < T ∧ ∀ t ≥ T, |f t| ≤ M * Real.exp (α * t))
    (L : ℕ → ℝ)
    (hL : ∀ k ∈ Finset.range n,
      Tendsto (iteratedDeriv k (rlIntegral 0 ((n : ℝ) - ν) f)) (nhdsWithin (0 : ℝ) (Ioi 0)) (nhds (L k)))
    (hexpn : ∃ M T : ℝ, 0 < M ∧ 0 < T ∧ ∀ t ≥ T, |rlDeriv 0 ν f t| ≤ M * Real.exp (α * t))
    (hsα : α < s.re) (hs0 : 0 < s.re) :
    laplace (rlDeriv 0 ν f) s =
      s ^ (ν : ℂ) * laplace f s -
        Finset.sum (Finset.range n) (fun k => s ^ (n - k - 1 : ℂ) * (L k : ℂ)) := by sorry
end FractionalCalc
