-- Prove2me | Theorems.Thm_LiqProvision_Oligopoly_theorem_2_8
-- name    : LiqProvision.Oligopoly.theorem_2_8
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T12:41:41.893832+00:00
-- url     : https://prove2.me/theorems/7e3d4bf1-c28c-481d-b039-2145684784f9
-- title:
--   Theorem 2.8, p. 6 — compatibility iff max ℓₖ < min rₖ; unique client response, continuous and nondecreasing
-- statement:
--   Let $K\ge2$, $\gamma_c>0$, and let $P_1,\dots,P_K$ be admissible price schedules with limiting marginal prices
--   $$\ell_k=\lim_{n\to-\infty}P_k'(n),\qquad r_k=\lim_{n\to\infty}P_k'(n)\qquad(k=1,\dots,K),$$
--   taken in the extended reals. Then $P_1,\dots,P_K$ are compatible if and only if
--   $$\bar\ell:=\max_k \ell_k<\bar r:=\min_k r_k .$$
--   In this case, writing $\mathbf P=(P_1,\dots,P_K)$:
--
--   1. for every type $y$ the client's problem $\max_{\mathbf n}J^{\mathbf P}(y;\mathbf n)$ has a unique solution $\mathbf n^{\mathbf P}(y)$;
--   2. for each $k$, the trade $y\mapsto n_k^{\mathbf P}(y)$ is continuous and nondecreasing on $\mathbb R$, and increasing on $\{y: n_k^{\mathbf P}(y)\ne0\}$.
--
--   This gives the compatibility criterion that makes unilateral deviations from a symmetric profile well defined.
--
--   **Formalization Note.** The model objects are those of `LiqProvision.Oligopoly.Model`. The limits $\ell_k,r_k$ are hypotheses: given extended reals with $P_k'(n)\to\ell_k$ as $n\to-\infty$ and $P_k'(n)\to r_k$ as $n\to\infty$ (they exist because admissible schedules are convex). Part (b) is stated for every response function of the client, which by (a) is $\mathbf n^{\mathbf P}$. Part (c) of the theorem (the image of $n_k^{\mathbf P}$) is not formalized.
-- source:
--   Herdegen, Muhle-Karbe and Stebegg, Liquidity Provision with Adverse Selection and Inventory Costs, arXiv:2107.12094v1, p. 6, Theorem 2.8 (a), (b), (2.3), (2.4)

import Mathlib
import Definitions.Def_LiqProvision_Oligopoly_Model

namespace LiqProvision.Oligopoly
open Filter Topology in
theorem theorem_2_8 (M : Params) (hK : 2 ≤ M.K) (hγc : 0 < M.γc)
    (Q : Fin M.K → ℝ → ℝ) (hQ : ∀ k, Admissible M (Q k)) (ℓ r : Fin M.K → EReal)
    (hℓ : ∀ k, Tendsto (fun n => ((deriv (Q k) n : ℝ) : EReal)) atBot (𝓝 (ℓ k)))
    (hr : ∀ k, Tendsto (fun n => ((deriv (Q k) n : ℝ) : EReal)) atTop (𝓝 (r k))) :
    (Compatible M Q ↔ Finset.univ.sup ℓ < Finset.univ.inf r) ∧
    (Compatible M Q →
      (∀ y, ∃! n, IsClientMax M Q y n) ∧
      ∀ resp : ℝ → Fin M.K → ℝ, IsResponse M Q resp → ∀ k : Fin M.K,
        Continuous (fun y => resp y k) ∧ Monotone (fun y => resp y k) ∧
          StrictMonoOn (fun y => resp y k) {y | resp y k ≠ 0}) := by sorry
end LiqProvision.Oligopoly
