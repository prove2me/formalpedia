-- Prove2me | Theorems.Thm_Grothendieck_vietoris_pos
-- name    : Grothendieck.vietoris_pos
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-02T15:04:52.358058+00:00
-- url     : https://prove2.me/theorems/e1890f69-c81d-42c3-baef-5a596b5ecb98
-- title:
--   Positivity of the cosine series of $E_r$ on $(0,\pi)$
-- statement:
--   For every integer $r\ge2$ and every $t\in(0,\pi)$,
--
--   $$
--   0<\sum_{k\ge0}\frac{(1/2)_k(1/2)_k}{(r/2+1)_k\,k!}\cos(kt),
--   $$
--
--   i.e. the real part of ${}_2F_1(1/2,1/2;r/2+1;e^{it})$ is positive: the cosine series of the paper's $E_r$ has no zeros on the open upper semicircle.
--
--   The paper invokes Vietoris's theorem for this (Andrews–Askey–Roy, Theorem 7.3.5). This node proves the instance without it, from the Beta representation of ${}_2F_1$. With $v(x)=(1-xe^{it})^{-1/2}$ and $D=1-2x\cos t+x^2>0$, one has $\operatorname{Re}(v^2)=(1-x\cos t)/D$ and $\operatorname{Im}(v^2)=x\sin t/D$, so
--
--   $$\big(\operatorname{Re}v\big)^2=\big(\operatorname{Im}v\big)^2+\frac{1-x\cos t}{D},$$
--
--   which is positive on $[0,1]$ because $x\cos t<1$ there; by continuity from $x=0$, where $v=1$, the real part is in fact positive. The coefficient of $x^k$ in $v$ is $(1/2)_k/k!$, and the Beta integral
--
--   $$\int_0^1x^{k-1/2}(1-x)^{r/2-1/2}dx=\frac{\Gamma(k+1/2)\Gamma((r+1)/2)}{\Gamma(k+r/2+1)}$$
--
--   turns $(1/2)_k/k!$ into the ratio $(1/2)_k/(r/2+1)_k$ up to the constant $\Gamma(1/2)\Gamma((r+1)/2)/\Gamma(r/2+1)$. Hence the series equals that constant times $\int_0^1x^{-1/2}(1-x)^{r/2-1/2}\operatorname{Re}v(x)\,dx$, an integral of a positive function.
--
--   **Formalization Note** Termwise integration is justified by the domination $(1-x)^{-1/2}$. This is the remaining input to Lemma 3.5, together with the evaluation at $t=\pi$.
-- source:
--   Briët, de Oliveira Filho, Vallentin, *Grothendieck inequalities for semidefinite programs with rank constraint*, Theory of Computing 10(4), 2014, pp. 77-105 — Claim 3.6, p. 90, and Lemma 3.5, p. 89.

import Mathlib
import Definitions.Def_Grothendieck_Series

open scoped BigOperators Real

namespace Grothendieck

/-- **Positivity of the cosine series of `E_r` (Vietoris's theorem for these parameters).**
For `r ≥ 2` and `t ∈ (0, π)`, `Re ₂F₁(1/2,1/2; r/2+1; e^{it}) > 0`. -/
theorem vietoris_pos (r : ℕ) (hr : 2 ≤ r) (t : ℝ) (ht0 : 0 < t) (ht1 : t < Real.pi) :
    0 < ∑' k : ℕ, (risingFact (1/2) k * risingFact (1/2) k
      / (risingFact ((r:ℝ)/2 + 1) k * (k.factorial : ℝ))) * Real.cos (k * t) := by sorry

end Grothendieck
