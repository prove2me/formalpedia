-- Prove2me | Theorems.Thm_Freiman_perron_formula
-- name    : Freiman.perron_formula
-- status  : Proved
-- author  : @tp
-- created : 2026-09-08T23:21:55.494777+00:00
-- url     : https://prove2.me/theorems/7b115472-326e-4565-8df6-5f2dbd772882
-- title:
--   Perron's formula for finite Lagrange values
-- statement:
--   Let $b=(b_n)_{n\ge0}$ be a sequence of positive integers, let $\xi=C(b)=[0;b_0,b_1,\ldots]$, and let
--   $$
--   P_n=b_n+[0;b_{n-1},\ldots,b_0]+[0;b_{n+1},b_{n+2},\ldots].
--   $$
--   The finite backward term is zero at $n=0$. For every real number $t$,
--   $$
--   \limsup_{q\to\infty}\frac{1}{q\delta(q\xi)}=t
--   \quad\Longleftrightarrow\quad
--   \limsup_{n\to\infty}P_n=t,
--   $$
--   where $q$ ranges over the positive integers and $\delta(x)$ is the distance to the nearest integer. Both equalities refer to the finite real value $t$.
--
--   This is the finite-value form of Perron's formula used to identify the Lagrange spectra.
-- source:
--   Freiman's Hall ray: Proof report and corrected English text, 8 September 2026, Theorem 1.2, p. 8, restricted to finite real values; the digit index is shifted by one.

import Definitions.Def_Freiman_cfValue
import Definitions.Def_Freiman_lagrangeSpectrum

namespace Freiman

theorem perron_formula (b : ℕ → ℕ+) (t : ℝ) :
    HasFiniteLimsup (fun n : ℕ => approximationValue (cfValue b) (n + 1)) t ↔
    HasFiniteLimsup (perronValue b) t := by
  sorry

end Freiman
