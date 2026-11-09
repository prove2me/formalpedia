-- Prove2me | Theorems.Thm_LinearChoresCLS_lemma_7_3
-- name    : LinearChoresCLS.lemma_7_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T21:52:04.69522+00:00
-- url     : https://prove2.me/theorems/2a1b34e0-bd3b-4e5f-aef3-eb3f9baedebf
-- title:
--   Lemma 7.3 — price bounds at every equilibrium of the completed market
-- statement:
--   Let $I=(A,c,\varepsilon)$ with $n\ge1$, $\varepsilon>0$, and let $(p,z)$ be a competitive equilibrium of the completed market $f(I)$. Then:
--
--   1. $(1+t)^{-3}\le p_\ell\le(1+t)^3$ for every chore $\ell$;
--   2. for every chain $(j,j')$, layer $k$ and sign $\sigma\in\{+,-\}$,
--   $$
--   S_{(j,j'),k}\,p^\sigma_{(j,j'),k}<B_{(j,j'),k},\qquad p^\sigma_{(j,j'),k}<p_{\max}\ \Longrightarrow\ \sum_{a\in N^\sigma_{\mathrm{out},k}}B_a<S_{(j,j'),k}\,p^\sigma_{(j,j'),k};
--   $$
--   3. $p_0\le p_j\le(1+t)p_0$ for every $j\in[n]$.
--
--   These bounds prepare the exclusion of undesignated choices (Lemma 7.4) and the price conditions of every gadget.
--
--   **Formalization Note** $N^\sigma_{\mathrm{out},k}$ are the agents outside the layer-$k$ gadget with positive allocation of $p^\sigma_{(j,j'),k}$; $p_{\max}$ is the largest price over all chores.
--
--   Differences from the source:
--   - encoding: chain (j, j′), layer k, sign σ ∈ {+, −} → π : Pair n, k : Fin L, σ : Bool (true = +); reason: index conventions; same instances
-- source:
--   Liu–Ma–Tao–Yang–Zheng, Competitive Equilibrium for Linear Chores is CLS-complete, arXiv:2611.06589 (held version, sha256 85d34a9e048d151ecff70a8614b9c2dd44307d5cf60faba74d14b2dd7eedc0b5), Lemma 7.3, Eq. (7.5), p.34

import Mathlib
import Definitions.Def_LinearChoresCLS_CompletedMarket

open Finset NetworkEquilibriumCLS.LinearNash

namespace LinearChoresCLS

/-- **Lemma 7.3 (Price bounds)** (arXiv:2611.06589, held version sha256 85d34a9e…, p.34). Let
`(p, z)` be an equilibrium of the completed market `f(I)` (`n ≥ 1`, `ε > 0`, parameters (7.1)).
(1) `(1 + t)^{−3} ≤ p_ℓ ≤ (1 + t)³` for every chore `ℓ`. (2) For every chain `(j, j′)`, layer `k`
and sign `σ ∈ {+, −}`: `S_{(j,j′),k} p^σ_{(j,j′),k} < B_{(j,j′),k}`, and if `p^σ_{(j,j′),k} < p_max`
then `∑_{a ∈ N^σ_{out,k}} B_a < S_{(j,j′),k} p^σ_{(j,j′),k}` (7.5). (3) `p₀ ≤ p_j ≤ (1 + t)p₀` for
every `j ∈ [n]`.

**Formalization Note.** `N^σ_{out,k}` (`outUsers`) are the agents outside the layer-`k` gadget
with `z_{a, p^σ} > 0`; `p_max` is the largest price over all chores; `σ = true` is `+`. -/
theorem lemma_7_3 {n : ℕ} (hn : 0 < n) (P : Quadratic n) (ε : ℚ) (hε : 0 < ε)
    (p : Chore n (chainLength P ε) → ℝ) (z : Agent n (chainLength P ε) → Chore n (chainLength P ε) → ℝ)
    (hCE : (completedMarket P ε).IsCE p z) :
    (∀ ℓ, ((1 + tParam P ε) ^ 3)⁻¹ ≤ p ℓ ∧ p ℓ ≤ (1 + tParam P ε) ^ 3) ∧
    (∀ (π : Pair n) (k : Fin (chainLength P ε)) (σ : Bool),
      gadgetSupply P (tParam P ε) π k.val * p (Sum.inr (π, k, σ)) <
          gadgetEarn P (tParam P ε) π k.val ∧
      (p (Sum.inr (π, k, σ)) < pmax p →
        ∑ a ∈ outUsers z π k σ, (completedMarket P ε).earn a <
          gadgetSupply P (tParam P ε) π k.val * p (Sum.inr (π, k, σ)))) ∧
    (∀ i : Fin n, p (Sum.inl 0) ≤ p (Sum.inl i.succ) ∧
      p (Sum.inl i.succ) ≤ (1 + tParam P ε) * p (Sum.inl 0)) := by sorry

end LinearChoresCLS
