-- Prove2me | Theorems.Thm_ImpulseNMFG_Verification_theorem_2_12
-- name    : ImpulseNMFG.Verification.theorem_2_12
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-19T01:15:33.338799+00:00
-- url     : https://prove2.me/theorems/c6c7bb39-ec6e-4e1e-99f8-167ca3b124ba
-- title:
--   Theorem 2.12, p. 10 — regular N-player QVI solution verifies a Nash equilibrium
-- statement:
--   Consider the $N$-player impulse game on a nonempty open domain $S\subseteq\mathbb R^d$ with diffusion generator $\mathcal L V=b\cdot\nabla V+\tfrac12\operatorname{tr}(\sigma\sigma^{t}D^2V)$. Let $V_1,\ldots,V_N$ be real functions on $S$ and let $\xi_i:S\to Z_i$ be such that, for every $y\in S$,
--   $$
--   \{\xi_i(y)\}=\arg\min_{\delta\in Z_i}\bigl\{V_i(\Gamma^i(y,\delta))+\phi_i(y,\delta)\bigr\}. \tag{2.10}
--   $$
--   Put $\mathcal M_iV_i(y)=V_i(\Gamma^i(y,\xi_i(y)))+\phi_i(y,\xi_i(y))$, $\mathcal H_{i,j}V_i(y)=V_i(\Gamma^j(y,\xi_j(y)))+\psi_{i,j}(y,\xi_j(y))$, $D_i=\{\mathcal M_iV_i-V_i>0\}$ and $W_i=S\cap\bigcap_{j\ne i}D_j$. Assume, for every $i$:
--
--   1. $V_i$ solves the QVI system (2.13): $V_i\to h_i$ at $\partial S$; $\mathcal M_jV_j-V_j\ge0$ on $S$; $\mathcal H_{i,j}V_i=V_i$ where $\mathcal M_jV_j=V_j$ ($j\ne i$); and $\min\{\mathcal LV_i-\rho_iV_i+f_i,\ \mathcal M_iV_i-V_i\}=0$ on $W_i\setminus\partial D_i$;
--   2. $V_i\in C^2(W_i\setminus\partial D_i)\cap C^1(W_i)\cap C(\overline{W_i})$ and $V_i$ has polynomial growth;
--   3. $\partial D_i$ is a Lipschitz surface and $V_i$ has locally bounded first and second derivatives in a neighbourhood of $\partial D_i$.
--
--   Let $x\in S$, set $A_i^*=\{y\in S:\mathcal M_iV_i(y)=V_i(y)\}$ and $\varphi^*=((A_1^*,\xi_1),\ldots,(A_N^*,\xi_N))$, and assume $\varphi^*\in\Phi_x$ and that each $\partial D_i$ is negligible for player $i$ at $x$. Then $\varphi^*$ is a Nash equilibrium and, for every player $i$,
--   $$
--   V_i(x)=J^i(x;\varphi^*).
--   $$
--   This is the paper's verification theorem: a regular solution of the coupled quasi-variational inequalities certifies both an equilibrium and its costs.
--
--   **Formalization Note** The candidate profile is built from $V$ and $\xi$, not chosen freely; the closedness of $A_i^*$ and the continuity of $\xi_i$ are part of $\varphi^*\in\Phi_x$. The equality $V_i(x)=J^i$ holds on every admissible realization of $\varphi^*$. The boundary condition is a limit within $S$ (as on p. 9), (2.13d) and the $C^2$ condition are taken off $\partial D_i$, and $W_i$ includes the intersection with $S$ so that $W_i=S$ when $N=1$. A nonzero player count is explicit through `NeZero N`. The hypothesis that $\partial D_i$ is negligible (the time $X$ spends on $\partial D_i$ has Lebesgue measure zero along every admissible deviation) is added to the page. It is the occupation-time hypothesis of Øksendal's Theorem 10.4.1, whose proof the paper cites for its approximation step; without it the statement fails for degenerate $\sigma$, because a path can run along $\partial D_i$, where (2.13d) constrains nothing.
-- source:
--   Basei, Cao, Guo, Nonzero-sum stochastic games and mean-field games with impulse controls, arXiv:1901.08085v4, p. 10, Theorem 2.12

import Mathlib
import Definitions.Def_ImpulseNMFG_Verification_Game
import Definitions.Def_ImpulseNMFG_Verification_QVI
set_option autoImplicit false

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal
open ImpulseGames.Verification (State IsBrownianBasis)

namespace ImpulseNMFG.Verification
noncomputable section
/-- Basei, Cao, Guo, Nonzero-sum stochastic games and mean-field games with impulse controls,
arXiv:1901.08085v4, p. 10, Theorem 2.12.
The N-player candidate defined by A_i*={M_i V_i−V_i=0} is Nash and its costs are V_i(x).
Φ_x requires an admissible realization; the conclusion ranges over all such realizations.
The SDE is the published Itô SolvesFrom on a usual-conditions Brownian filtration.
Formalization Note: `hocc` (the time X spends on ∂D_i is Lebesgue-null along every admissible
deviation) is added to the page's hypotheses. It is the occupation-time hypothesis of
Øksendal's Theorem 10.4.1, whose proof the paper cites for (a)–(c); without it the statement
fails for degenerate σ (a path running along ∂D_i, where (2.13d) imposes nothing on f_i). -/
theorem theorem_2_12 {N d M : ℕ} [NeZero N] {Ω : Type*} [m : MeasurableSpace Ω]
    (P : Measure Ω) (𝔽 : Filtration ℝ≥0 m) (W : ℝ≥0 → Ω → (Fin M → ℝ))
    (hW : IsBrownianBasis P 𝔽 W) (G : Game N d M) (hG : G.Standing)
    (V : Fin N → State d → ℝ) (ξ : (i : Fin N) → State d → G.Imp i)
    (h210 : ∀ i, IsUniqueMinimizer G V ξ i)
    (hi : ∀ i, SolvesQVI G V ξ i)
    (hii : ∀ i, Regular G V ξ i)
    (hiii : ∀ i, BoundaryRegular G V ξ i)
    (x : State d) (hx : x ∈ G.S)
    (hocc : ∀ i, BoundaryNegligible P 𝔽 W G V ξ x i)
    (hadm : InPhi P 𝔽 W G x (starProfile G V ξ)) :
    IsNash P 𝔽 W G x (starProfile G V ξ) ∧
    ∀ (i : Fin N) (Y : ℕ → ℝ≥0 → Ω → State d),
      IsAdmissible P 𝔽 W G x (starProfile G V ξ) Y →
      V i x = cost P G x (starProfile G V ξ) Y i := by sorry
end
end ImpulseNMFG.Verification
