-- Prove2me | Theorems.Thm_KhintchineTwoRegime_sixProfile_mem_Cn
-- name    : KhintchineTwoRegime.sixProfile_mem_Cn
-- status  : Open
-- author  : @Mr Robbins
-- created : 2026-11-23T03:33:46.483876+00:00
-- url     : https://prove2.me/theorems/726650de-5a97-4873-a663-7be18e966a75
-- title:
--   Six-coordinate profile belongs to $\mathcal C_n(\tau)$
-- statement:
--   For $n\ge6$ and $\tau\in[d_0,d_1]$, where $d_0=\sqrt{2-\sqrt2}$ and $d_1=\sqrt{2-\sqrt{966}/22}$, the six-coordinate candidate
--   $$
--   \omega^{(6)}_\tau=(r,r,r,r,s,s,0,\ldots,0),\qquad r=\frac{2-\tau^2}{2\sqrt2},\quad s=\sqrt{\tau^2-\frac{\tau^4}{4}-\frac12},
--   $$
--   is a proper unit vector whose Euclidean distance from $\omega^*=(1/\sqrt2,1/\sqrt2,0,\ldots,0)$ is $\tau$. Thus $\omega^{(6)}_\tau\in\mathcal C_n(\tau)$.
--
--   This is the membership assertion in the displayed candidate computation in the proof of Theorem 2.
-- source:
--   Fang–Wang, A Two-regime Khintchine Inequality and an Improved Bound on the Degree-1 Fourier Weight for Linear Threshold Functions, arXiv:2608.27908v2, Theorem 2 and its proof, p.8 ('The displayed candidate is proper').

import Mathlib
import Definitions.Def_KhintchineTwoRegime_Cn
import Definitions.Def_KhintchineTwoRegime_sixProfile

theorem KhintchineTwoRegime.sixProfile_mem_Cn (n : ℕ) (hn : 6 ≤ n) (τ : ℝ)
    (hτ : τ ∈ Set.Icc (Real.sqrt (2 - Real.sqrt 2)) (Real.sqrt (2 - Real.sqrt 966 / 22))) :
    sixProfile n τ ∈ Cn n τ := by sorry
