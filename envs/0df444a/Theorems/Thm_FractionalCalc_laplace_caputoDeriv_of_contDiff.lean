-- Prove2me | Theorems.Thm_FractionalCalc_laplace_caputoDeriv_of_contDiff
-- name    : FractionalCalc.laplace_caputoDeriv_of_contDiff
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-11-21T15:48:50.299918+00:00
-- url     : https://prove2.me/theorems/c399551c-1479-4939-8dde-ff2c1f60685c
-- title:
--   Laplace transform of the Caputo fractional derivative (Eq. 24), for $C^n$ functions on the line
-- statement:
--   Let $\nu>0$, $n=\lceil\nu\rceil$, and let $f:\mathbb R\to\mathbb R$ be $C^n$ on the whole line, of exponential order $\alpha$, with $f^{(n)}$ also of exponential order $\alpha$. For $\operatorname{Re}s>\max(\alpha,0)$,
--   $$\mathcal L\big[{}^{C}D_{0+}^{\nu}f\big](s)=s^{\nu}\mathcal L[f](s)-\sum_{k=0}^{n-1}s^{\,\nu-k-1}\,f^{(k)}(0).$$
--   This is Eq. (24) of the source. Unlike the Riemann–Liouville formula, the initial terms are the classical derivatives of $f$ at $0$, which is why the Caputo derivative suits physical initial conditions.
--
--   **Formalization Note** The initial values are the two sided derivatives `iteratedDeriv k f 0`. Regularity is therefore asked on all of $\mathbb R$ and not only on $[0,\infty)$, so that these agree with the right hand values $f^{(k)}(0+)$ of the source.
-- source:
--   F. G. Rodrigues & E. C. de Oliveira, Rev. Bras. Ens. Fís. 37(3), 3305 (2015), https://doi.org/10.1590/S1806-11173731842, §4, Eq. (24).

import Mathlib
import Definitions.Def_FractionalCalc_rlIntegral
import Definitions.Def_FractionalCalc_caputoDeriv
import Definitions.Def_QueueingFundamentals_Transient_laplace
open MeasureTheory Set Classical QueueingFundamentals.Transient

namespace FractionalCalc
theorem laplace_caputoDeriv_of_contDiff (ν α : ℝ) (f : ℝ → ℝ) (s : ℂ)
    (hν : 0 < ν) (n : ℕ) (hn : n = Nat.ceil ν)
    (hsmooth : ContDiff ℝ n f)
    (hexp : ∃ M T : ℝ, 0 < M ∧ 0 < T ∧ ∀ t ≥ T, |f t| ≤ M * Real.exp (α * t))
    (hexpn : ∃ M T : ℝ, 0 < M ∧ 0 < T ∧ ∀ t ≥ T, |iteratedDeriv n f t| ≤ M * Real.exp (α * t))
    (hsα : α < s.re) (hs0 : 0 < s.re) :
    laplace (caputoDeriv 0 ν f) s =
      s ^ (ν : ℂ) * laplace f s -
        Finset.sum (Finset.range n) (fun k => s ^ (ν - k - 1 : ℂ) * Complex.ofReal (iteratedDeriv k f (0 : ℝ))) := by sorry
end FractionalCalc
