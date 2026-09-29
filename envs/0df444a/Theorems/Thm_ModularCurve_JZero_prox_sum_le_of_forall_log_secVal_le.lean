-- Prove2me | Theorems.Thm_ModularCurve_JZero_prox_sum_le_of_forall_log_secVal_le
-- name    : ModularCurve.JZero.prox_sum_le_of_forall_log_secVal_le
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:41.339792+00:00
-- url     : https://prove2.me/theorems/7bf61f0f-19e4-53a1-81f1-b04db0b912f1
-- title:
--   One-sided archimedean proximity bound with explicit normalisation
-- statement:
--   Let $N \ge 1$ and let $\bar F_N$ denote `modularFunctionFieldBar N`, the base change to $\overline{\mathbb Q}$ of the full modular function field of level $N$ inside Laurent series. Let $s : \mathrm{Fin}\,r \to \bar F_N$ satisfy `IsEmbBasis N s`, i.e. $s$ is linearly independent over $\overline{\mathbb Q}$ and spans the Riemann–Roch space of `embDivisor N` $=(\deg_{\mathrm{emb}} N)\cdot\delta_{\bar\infty}$, where $\bar\infty$ is the place `cuspInftyBar N`; let $t \in \bar F_N$ have $\mathrm{ord}_{\bar\infty}(t)=1$. For a place $y$ write $x_y =$ `evalVec s y` for the vector with entries $y.\mathrm{evalAt}(s_i \cdot s_{\mathrm{piv}(y)}^{-1})$, and for $u \in \bar F_N$ put $u(y)=$ `secVal s y k u` $= y.\mathrm{evalAt}(u\, s_{\mathrm{piv}(y)}^{-k})$ and $u^{\mathrm{reg}}(\bar\infty)=$ `regVal s (cuspInftyBar N) t k e u` $= \bar\infty.\mathrm{evalAt}(u\, s_{\mathrm{piv}(\bar\infty)}^{-k} t^{-e})$. The assertion is the existence of a real constant $c$ such that for every ring homomorphism $\sigma : \overline{\mathbb Q} \to \mathbb C$, every $k \in \mathbb N$, every nonzero $u$ in the Riemann–Roch space of $k\cdot$`embDivisor N`, every divisor $B$ with $B(w)=\mathrm{ord}_w(u)+k\,(\mathrm{embDivisor}\,N)(w)$ for all places $w$, and every $S \in \mathbb R$ such that $\log\|\sigma(u(y))\| - k\log(\sup_i \|\sigma(x_y)_i\|) \le S$ for all places $y$ with $B(y)=0$, both of the following hold: first, $\sum_{w} B(w)\,\mathrm{prox}(x_{\bar\infty},x_w) \le k\log(\sup_i\|\sigma(x_{\bar\infty})_i\|) - \log\|\sigma(u^{\mathrm{reg}}(\bar\infty))\| + S + ck$, the sum being over $B$ with the value at $\bar\infty$ erased; second, for every place $v$ with $B(v)=0$, $\sum_w B(w)\,\mathrm{prox}(x_v,x_w) \le k\log(\sup_i\|\sigma(x_v)_i\|) - \log\|\sigma(u(v))\| + S + ck$. Here $\mathrm{prox}(x,x') = \log\sup_i\|\sigma x_i\| + \log\sup_j\|\sigma x'_j\| - \log\sup_{i,j}\|\sigma(x_i x'_j - x_j x'_i)\|$ is the logarithmic chordal proximity. The constant $c$ is uniform in $\sigma$, $k$, $u$, $B$ and $S$.
--
--   This is the one-sided, explicitly normalised form of the archimedean first-main-theorem (Poisson–Jensen) comparison between the proximity sum of the zero-cycle of a section $u \in L(kE)$ and the normalised logarithmic size of $u$: in the two-sided comparison [`ModularCurve.JZero.jensen_arch_embedding`](thm.html#ModularCurve.JZero.jensen_arch_embedding) the additive constant exists only abstractly, whereas here it is replaced by any upper bound $S$ for the normalised section off the support of $B$, at the cost of a term $ck$. It feeds the archimedean local estimate [`ModularCurve.JZero.jensen_arch_at_le_of_nonCuspidal`](thm.html#ModularCurve.JZero.jensen_arch_at_le_of_nonCuspidal) in the height-theoretic analysis on $J_0(N)$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_JZero_prox_sum_le_of_forall_log_secVal_le.lean

import Definitions.Def_ModularCurve_JZeroHeightForm
import Definitions.Def_AlgebraicCurve_ChordalProximity

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open AlgebraicCurve ModularCurve

theorem ModularCurve.JZero.prox_sum_le_of_forall_log_secVal_le (N : ℕ) [NeZero N] {r : ℕ}
    (s : Fin r → modularFunctionFieldBar N) (hs : IsEmbBasis N s)
    (t : modularFunctionFieldBar N) (ht : (cuspInftyBar N).ord t = 1) :
    ∃ c : ℝ, ∀ (σ : (AlgebraicClosure ℚ) →+* ℂ) (k : ℕ) (u : modularFunctionFieldBar N), u ≠ 0 →
      u ∈ riemannRochSpace ((k : ℤ) • embDivisor N) →
      ∀ B : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar N),
      (∀ w, B w = w.ord u + ((k : ℤ) • embDivisor N) w) →
      ∀ S : ℝ, (∀ y : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N), B y = 0 →
          Real.log ‖σ (secVal s y k u)‖ - (k : ℝ) * Real.log (⨆ i, ‖σ (evalVec s y i)‖) ≤ S) →
        ((B.erase (cuspInftyBar N)).sum fun w n => (n : ℝ) *
            prox (fun a => ‖σ a‖) (evalVec s (cuspInftyBar N)) (evalVec s w))
          ≤ (k : ℝ) * Real.log (⨆ i, ‖σ (evalVec s (cuspInftyBar N) i)‖)
              - Real.log ‖σ (regVal s (cuspInftyBar N) t k (B (cuspInftyBar N)).toNat u)‖ + S + c * k ∧
        ∀ v : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N), B v = 0 →
          (B.sum fun w n => (n : ℝ) * prox (fun a => ‖σ a‖) (evalVec s v) (evalVec s w))
            ≤ (k : ℝ) * Real.log (⨆ i, ‖σ (evalVec s v i)‖) - Real.log ‖σ (secVal s v k u)‖ + S + c * k := by sorry
