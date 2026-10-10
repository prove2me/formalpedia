-- Prove2me | Theorems.Thm_GraphLQGame_Equilibrium_value_identity
-- name    : GraphLQGame.Equilibrium.value_identity
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T12:28:08.385975+00:00
-- url     : https://prove2.me/theorems/232a232c-c293-4c1e-954f-637e5e59a52f
-- title:
--   §4.6, p. 29 — $\frac1n\sum_i v_i(t,x) = \frac{|P(t)x|^2}{2\mathrm{Tr}(P(t))} - \frac{\sigma^2}{2}\log\frac{\mathrm{Tr}(P(t))}{nf'(T-t)}$
-- statement:
--   Let $G$ be a finite transitive graph on $n$ vertices without isolated vertices, $c,\sigma,T>0$, $f$ the solution of $f'=cQ_G'(f)$, $f(0)=0$ on $[0,T]$, $P=P_G$, $F^i$ as in (4.13), $h_i(t)=\frac{\sigma^2}{2}\int_t^T\mathrm{Tr}(F^i(s))\,ds$ (4.9), and $v_i(t,x)=\frac12x^\top F^i(t)x+h_i(t)$. For $t\in[0,T]$ and $x\in\mathbb R^n$,
--   $$\frac1n\sum_{i=1}^nv_i(t,x)=\frac{|P(t)x|^2}{2\,\mathrm{Tr}(P(t))}-\frac{\sigma^2}{2}\log\frac{\mathrm{Tr}(P(t))}{n\,f'(T-t)} .$$
--
--   At $t=0$, $x=X(0)$ this is the value formula (2.6).
--
--   **Formalization Note** The page writes $v_k$ under $\sum_i$, a misprint for $v_i$, which is what is stated. $|y|^2=\sum_ky_k^2$; $f'(T-t)$ is $cQ_G'(f(T-t))$.
-- source:
--   Lacker, Soret, A case study on stochastic games on large graphs in mean field and sparse regimes, arXiv:2005.14102v2 (2021), §4.6, p. 29, final display (with (4.5), (4.9), (4.13))

import Mathlib
import Definitions.Def_GraphLQGame_Equilibrium_Graph
import Definitions.Def_GraphLQGame_Equilibrium_Equilibrium
import Definitions.Def_GraphLQGame_Equilibrium_NashSystem

namespace GraphLQGame.Equilibrium

/-- Lacker–Soret, arXiv:2005.14102v2, §4.6, p. 29, final display: with
`v_i(t, x) = ½ xᵀ Fⁱ(t) x + h_i(t)`, `Fⁱ` from (4.13) and `h_i(t) = (σ²/2) ∫_t^T Tr(Fⁱ(s)) ds` (4.9),
for `t ∈ [0, T]` and `x ∈ ℝⁿ`,
`(1/n) Σ_i v_i(t, x) = |P(t)x|² / (2 Tr(P(t))) − (σ²/2) log(Tr(P(t)) / (n f'(T − t)))`.

Formalization Note: the page writes `v_k` under `Σ_i`, a misprint for `v_i`, which is what is
stated. `|y|²` is `Σ_k y_k²`; `f'(T − t)` is written `c Q_G'(f(T − t))`, its value by the ODE. -/
theorem value_identity {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (hT : IsTransitive G) (hN : NoIsolated G) (c σ T : ℝ) (hc : 0 < c) (hσ : 0 < σ)
    (hTpos : 0 < T) (f : ℝ → ℝ) (hf : IsFSol c T (QG G) f) (t : ℝ)
    (ht : t ∈ Set.Icc (0 : ℝ) T) (x : Fin n → ℝ) :
    (n : ℝ)⁻¹ * ∑ i : Fin n,
        (1 / 2 * (x ⬝ᵥ (Fmat G c T f i t).mulVec x) + hfun G c σ T f i t) =
      (∑ k : Fin n, ((PG G c T f t).mulVec x k) ^ 2) / (2 * (PG G c T f t).trace) -
        σ ^ 2 / 2 * Real.log ((PG G c T f t).trace /
          (n * (c * deriv (QG G) (f (T - t))))) := by sorry

end GraphLQGame.Equilibrium
