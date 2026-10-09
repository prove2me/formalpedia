-- Prove2me | Theorems.Thm_IntMul_HvdH_theorem_4_2
-- name    : IntMul.HvdH.theorem_4_2
-- status  : Proved
-- author  : @avi
-- created : 2026-10-08T17:33:57.239075+00:00
-- url     : https://prove2.me/theorems/b2d7a424-60ac-47c7-898d-88e6b4687e8b
-- title:
--   Theorem 4.2 — resampling identity $\mathcal T\mathcal P_s\mathcal F_s=\mathcal P_t\mathcal F_t\mathcal S$
-- statement:
--   Let $s$ and $t>s$ be positive integers with $\gcd(s,t)=1$, and let $\alpha>0$. Let $\mathcal F_n$ be the normalized DFT of length $n$, let $\mathcal S,\mathcal T:\mathbb C^s\to\mathbb C^t$ be the Gaussian resampling maps
--   $$(\mathcal Su)_k=\alpha^{-1}\sum_{j\in\mathbb Z}e^{-\pi\alpha^{-2}s^2(k/t-j/s)^2}u_j,\qquad(\mathcal Tu)_k=\sum_{j\in\mathbb Z}e^{-\pi\alpha^2t^2(k/t-j/s)^2}u_j,$$
--   and let $(\mathcal P_su)_j=u_{tj}$ and $(\mathcal P_tu)_k=u_{-sk}$, where indices are read modulo $s$ and modulo $t$ respectively. Then
--   $$\mathcal T\,\mathcal P_s\,\mathcal F_s=\mathcal P_t\,\mathcal F_t\,\mathcal S .$$
--
--   This identity expresses a DFT of length $s$ in terms of a DFT of the larger length $t$. It is how Harvey and van der Hoeven replace transforms of prime length by transforms whose lengths are powers of two.
-- source:
--   D. Harvey, J. van der Hoeven, Integer multiplication in time O(n log n), Annals of Mathematics 193(2) (2021) 563-617, https://doi.org/10.4007/annals.2021.193.2.4 (preprint https://hal.science/hal-02070778v2), §4.1, Theorem 4.2, p. 24 (setting of §4.1: s < t positive, gcd(s,t)=1, alpha in (0,inf))

import Mathlib
import Definitions.Def_IntMul_HvdH_Resampling

namespace IntMul.HvdH

theorem theorem_4_2 (s t : ℕ) [NeZero s] [NeZero t] (hst : s < t) (hcop : Nat.Coprime s t)
    (α : ℝ) (hα : 0 < α) :
    (resT s t α).comp ((permS s t).comp (dft s)) =
      (permT s t).comp ((dft t).comp (resS s t α)) := by sorry

end IntMul.HvdH
