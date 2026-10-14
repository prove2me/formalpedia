-- Prove2me | Theorems.Thm_IntMul_HvdH_Dapprox_bound
-- name    : IntMul.HvdH.Dapprox_bound
-- status  : Proved
-- author  : @xuanji
-- created : 2026-10-11T23:19:45.467637+00:00
-- url     : https://prove2.me/theorems/e554d8b7-94f0-42fb-a200-545b66bfee5b
-- title:
--   Approximation of the diagonal resampling map $\mathcal D'$ (Lemma 4.8)
-- statement:
--   Let $p,s,t,\alpha$ be integers with $s\ge1$, $\alpha\ge2$ and $\alpha^2\le p$. Let $U_\ell\in\mathbb Z[i]$ with $|U_\ell|\le2^p$, so that $u_\ell=2^{-p}U_\ell$ lies in the unit disc. Put $\beta_\ell=t\ell/s-\lfloor t\ell/s+\tfrac12\rfloor$ and $d'_\ell=e^{\pi\alpha^2\beta_\ell^2}/2^{2\alpha^2-2}$. Then the output $Z_\ell$ of `Dapprox` (see `IntMul_HvdH_DiagApprox`) satisfies
--   $$2^p\bigl|2^{-p}Z_\ell-d'_\ell u_\ell\bigr|<3,$$
--   i.e. $\varepsilon(\tilde{\mathcal D}'u)<3$. This is Lemma 4.8 of Harvey–van der Hoeven, which has the bound $4$.
-- source:
--   Harvey, van der Hoeven, Integer multiplication in time O(n log n), Annals of Math. 193 (2021), https://hal.science/hal-02070778, Lemma 4.8 and Section 4.2 (definition of D)

import Definitions.Def_IntMul_HvdH_DiagApprox

namespace IntMul.HvdH
theorem Dapprox_bound (p s t α : ℕ) (hs : 0 < s) (hα : 2 ≤ α) (hαp : α ^ 2 ≤ p)
    (U : ℕ → ℤ × ℤ) (hU : ∀ l, ‖((U l).1 : ℂ) + ((U l).2 : ℂ) * Complex.I‖ ≤ 2 ^ p) (l : ℕ) :
    ‖(((Dapprox p s t α U l).1 : ℂ) + ((Dapprox p s t α U l).2 : ℂ) * Complex.I) -
      ((Real.exp (Real.pi * α ^ 2 * ((t * l : ℝ) / s - ⌊(t * l : ℝ) / s + 1 / 2⌋) ^ 2) /
        2 ^ (2 * α ^ 2 - 2) : ℝ) : ℂ) * (((U l).1 : ℂ) + ((U l).2 : ℂ) * Complex.I)‖ < 3 := by sorry
end IntMul.HvdH
