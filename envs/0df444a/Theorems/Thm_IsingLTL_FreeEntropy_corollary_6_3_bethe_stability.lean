-- Prove2me | Theorems.Thm_IsingLTL_FreeEntropy_corollary_6_3_bethe_stability
-- name    : IsingLTL.FreeEntropy.corollary_6_3_bethe_stability
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T00:13:31.679857+00:00
-- url     : https://prove2.me/theorems/fc6f9293-1497-4bd6-afca-d9c8e200fc37
-- title:
--   Corollary 6.3 (corrected constant) — $|\varphi_h-\varphi_{h^*}|\le c(|\beta|)\,\mathbb E[L^2]\,\|\tanh h-\tanh h^*\|^2_{\mathrm{MK}}$
-- statement:
--   There is a nondecreasing finite function $c(|\beta|)$ such that, whenever $P$ is a degree distribution with $\bar\rho<\infty$ and $h^*$ is a fixed point of the distributional identity (2.6) for some $\beta,B\in\mathbb R$, every real random variable $h$ satisfies
--   $$|\varphi_h(\beta,B)-\varphi_{h^*}(\beta,B)|\le c(|\beta|)\,\mathbb E[L^2]\,\|\tanh(h)-\tanh(h^*)\|^2_{\mathrm{MK}},$$
--   where $L\sim P$, so $\mathbb E[L^2]=\sum_l l^2P_l$.
--
--   The Bethe functional is stationary at fixed points of the recursion: perturbing the cavity law changes it only to second order.
--
--   **Formalization Note** The printed statement has $\bar P\bar\rho$ in place of $\mathbb E[L^2]$ and is false as printed: $\bar P\bar\rho=\sum_k k(k-1)P_k=\mathbb E[L(L-1)]$, which is smaller than $\mathbb E[L^2]$ whenever $P_1>0$. For $P=\delta_1$ (so $\bar\rho=0$ and $h^*\equiv B$ is a fixed point) the printed right side is $0$, while at $\beta=B=1$, $\varphi_{h\equiv B}-\varphi_{h\equiv0}\approx0.183$. The paper's own proof establishes the bound with $\mathbb E[L^2]$ (via (6.4)), which is the statement here. $h^*$ is any fixed point; $\tanh(h)$ denotes the image law.
-- source:
--   Dembo & Montanari, Ising Models on Locally Tree-Like Graphs, arXiv:0804.4726v3, p. 23, Corollary 6.3, (6.5) (constant corrected from $\bar P\bar\rho$ to $\mathbb E[L^2]$, as given by (6.4) on p. 23)

import Mathlib
import Definitions.Def_IsingLTL_FreeEntropy_BetheFunctional
import Definitions.Def_IsingLTL_FreeEntropy_MKDist

namespace IsingLTL.FreeEntropy

open MeasureTheory

/-- **Corollary 6.3, with the corrected constant** (Dembo–Montanari, *Ising Models on Locally
Tree-Like Graphs*, arXiv:0804.4726v3, p. 23, eq. (6.5)). There exist nondecreasing finite
`c(|β|)` such that if `ρ̄ < ∞` and `h*` is a fixed point of the distributional identity (2.6) for
some `β, B ∈ ℝ`, then for every random variable `h`
`|φ_h(β, B) − φ_{h*}(β, B)| ≤ c(|β|) E[L²] ‖tanh(h) − tanh(h*)‖²_MK`,
where `L ∼ P` and `E[L²] = ∑_l l² P_l`.

Formalization Note. **The printed statement has `P̄ ρ̄` where this one has `E[L²]`, and the
printed statement is false.** The proof ends "Noting that `E[L²] = P̄ρ̄` our thesis is merely the
bound (6.4)", but `P̄ρ̄ = ∑_k k(k − 1) P_k = E[L(L − 1)] < E[L²]` whenever `P₁ > 0`. For `P = δ₁`
(so `ρ = δ₁`, `ρ̄ = 0`, and `h* ≡ B` is a fixed point) the printed right side is `0`, while at
`β = B = 1`, `φ_{h≡B} − φ_{h≡0} ≈ 0.183`. What the proof establishes, through (6.4), is the
bound with `E[L²]`, stated here. "`ρ̄ < ∞`" is `ρ` with finite first moment (equivalently
`E[L²] < ∞`). `h` is given by its law `Q` and `h*` by its law `Q*` (any fixed point, not
necessarily the one supported on `[0, ∞)`); `tanh(h)` is the push-forward law. `c` is a real
function, monotone on `[0, ∞)`, chosen before `P`, `β`, `B` and the laws. The MK distance of two
laws on `[−1, 1]` is at most `2`, so the right side is finite; the inequality is stated in
`ℝ≥0∞`. -/
theorem corollary_6_3_bethe_stability :
    ∃ c : ℝ → ℝ, MonotoneOn c (Set.Ici 0) ∧
      ∀ (D : DegreeDist), D.RhoFiniteMean →
      ∀ (β B : ℝ) (Q Qs : ProbabilityMeasure ℝ), IsFixedPoint β B D Qs →
        ENNReal.ofReal |betheFunctional β B D Q - betheFunctional β B D Qs| ≤
          ENNReal.ofReal (c |β| * D.secondMoment) *
            mkDist ((Q : Measure ℝ).map Real.tanh) ((Qs : Measure ℝ).map Real.tanh) ^ 2 := by sorry

end IsingLTL.FreeEntropy
