-- Prove2me | Theorems.Thm_NonuniformKuramoto_CondI_sinusoid_lower_bound
-- name    : NonuniformKuramoto.CondI.sinusoid_lower_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T11:24:33.332239+00:00
-- url     : https://prove2.me/theorems/9c22ebbe-8dda-4624-b796-8219fba42726
-- title:
--   Proof of Theorem V.3, p. 22 — $a\sin x + b\sin y\ge\min\{a,b\}\sin(x+y)$ for $x,y\ge0$, $x+y\le\pi$
-- statement:
--   Let $a,b\ge0$ and $x,y\ge0$ with $\gamma:=x+y\le\pi$. Then
--
--   $$a\sin x+b\sin y\ \ge\ \min\{a,b\}\sin(\gamma).$$
--
--   In the proof of Theorem V.3, $x=\theta_m-\theta_k$ and $y=\theta_k-\theta_\ell$ are the distances of an oscillator $k$ to the two ends $m,\ell$ of the arc of length $\gamma$ containing all phases, and $a=a_{mk}$, $b=a_{\ell k}$ with $a_{ik}=P_{ik}\cos(\varphi_{ik})/D_i$. The inequality bounds the restoring coupling that shrinks the arc.
--
--   **Formalization Note** The page takes the minimum over $i\in\{m,\ell\}\setminus\{k\}$. When $k\notin\{m,\ell\}$ this is $\min\{a,b\}$ as stated here; when $k=m$ (or $k=\ell$) one of $x,y$ is $0$ and the claim reduces to $a_{\ell k}\sin\gamma\ge a_{\ell k}\sin\gamma$ (resp. $a_{mk}\sin\gamma\ge a_{mk}\sin\gamma$), so the two-variable form is the content of the step.
-- source:
--   Dörfler & Bullo, Synchronization and Transient Stability in Power Networks and Nonuniform Kuramoto Oscillators, arXiv:0910.5673v4, p. 22, proof of Theorem V.3, first display

import Mathlib
import Definitions.Def_NonuniformKuramoto_CondI_Model
import Definitions.Def_NonuniformKuramoto_CondI_Constants

namespace NonuniformKuramoto.CondI

/-- Proof of Theorem V.3, p. 22: if `x = θ_m − θ_k ≥ 0`, `y = θ_k − θ_ℓ ≥ 0` with `x + y = γ ≤ π`
and the weights `a = a_mk`, `b = a_ℓk` are nonnegative, then
`a sin x + b sin y ≥ min{a, b} sin γ`. -/
theorem sinusoid_lower_bound (a b x y γ : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hx : 0 ≤ x) (hy : 0 ≤ y)
    (hxy : x + y = γ) (hγ : γ ≤ Real.pi) :
    min a b * Real.sin γ ≤ a * Real.sin x + b * Real.sin y := by sorry

end NonuniformKuramoto.CondI
