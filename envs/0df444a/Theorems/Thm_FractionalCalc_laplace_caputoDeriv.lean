-- Prove2me | Theorems.Thm_FractionalCalc_laplace_caputoDeriv
-- name    : FractionalCalc.laplace_caputoDeriv
-- status  : Open
-- author  : @LG
-- created : 2026-11-20T16:41:20.868183+00:00
-- url     : https://prove2.me/theorems/bcd46f40-2172-4b59-a09b-5f9e42cc5e23
-- title:
--   Laplace transform of the Caputo fractional derivative (Eq. 24)
-- statement:
--   Let $\nu>0$, $n=\lceil\nu\rceil$, and let $f$ be $C^n$ on $[0,\infty)$, of exponential order $\alpha$, with $f^{(n)}$ also of exponential order $\alpha$. For $\operatorname{Re}s>\max(\alpha,0)$,
--   $$\mathcal L\big[{}^{C}D_{0+}^{\nu}f\big](s)=s^{\nu}\mathcal L[f](s)-\sum_{k=0}^{n-1}s^{\,\nu-k-1}\,f^{(k)}(0+).$$
--   This is Eq. (24) of the source. Unlike the Riemann–Liouville formula, the initial terms are the classical derivatives $f^{(k)}(0+)$, which is why the Caputo derivative suits physical initial conditions.
--
--   **Formalization Note** $C^n$ regularity up to $0$ (`ContDiffOn`) makes $f^{(k)}(0+)=f^{(k)}(0)$; this is the explicit standing convention for the source's "sufficiently well-behaved" (footnote 4).
-- source:
--   F. G. Rodrigues & E. C. de Oliveira, Rev. Bras. Ens. Fís. 37(3), 3305 (2015), https://doi.org/10.1590/S1806-11173731842, §4, Eq. (24).

import Mathlib
import Definitions.Def_FractionalCalc_rlIntegral
import Definitions.Def_FractionalCalc_caputoDeriv
import Definitions.Def_QueueingFundamentals_Transient_laplace
open MeasureTheory Set Classical QueueingFundamentals.Transient

namespace FractionalCalc
theorem laplace_caputoDeriv (ν α : ℝ) (f : ℝ → ℝ) (s : ℂ)
    (hν : 0 < ν) (n : ℕ) (hn : n = Nat.ceil ν)
    (hsmooth : ContDiffOn ℝ n f (Ici (0 : ℝ)))
    (hexp : ∃ M T : ℝ, 0 < M ∧ 0 < T ∧ ∀ t ≥ T, |f t| ≤ M * Real.exp (α * t))
    (hexpn : ∃ M T : ℝ, 0 < M ∧ 0 < T ∧ ∀ t ≥ T, |iteratedDeriv n f t| ≤ M * Real.exp (α * t))
    (hsα : α < s.re) (hs0 : 0 < s.re) :
    laplace (caputoDeriv 0 ν f) s =
      s ^ (ν : ℂ) * laplace f s -
        Finset.sum (Finset.range n) (fun k => s ^ (ν - k - 1 : ℂ) * Complex.ofReal (iteratedDeriv k f (0 : ℝ))) := by sorry
end FractionalCalc
