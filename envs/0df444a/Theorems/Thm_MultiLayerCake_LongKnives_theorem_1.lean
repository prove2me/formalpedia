-- Prove2me | Theorems.Thm_MultiLayerCake_LongKnives_theorem_1
-- name    : MultiLayerCake.LongKnives.theorem_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T23:08:50.365261+00:00
-- url     : https://prove2.me/theorems/00d43ebc-b757-459e-bc6a-4e0fe40bf04f
-- title:
--   Theorem 1, p. 5 — for a prime power q with m ≤ q ≤ n, a feasible contiguous group-birthday envy-free multi-division by q − 1 long knives exists
-- statement:
--   Consider an $m$-layered cake and $n$ agents, each with a choice function $c_i$ and closed preferences, and let $q$ be a prime power with $m\le q\le n$. Fix a birthday agent $b$. Then there is a multi-division $\mathcal A=(\mathcal A_1,\dots,\mathcal A_q)$ of the $m$-layered cake into $q$ layered pieces which is feasible, contiguous and obtained with $q-1$ long knives, such that for every $j^*\in[q]$ there is an assignment $\pi_{j^*}:[n]\to[q]$ with
--
--   1. $\pi_{j^*}(b)=j^*$;
--   2. $\mathcal A_{\pi_{j^*}(i)}\in c_i(\mathcal A)$ for every agent $i\neq b$;
--   3. for every $j\in[q]$,
--   $$\Big\lfloor\frac nq\Big\rfloor\le\big|\pi_{j^*}^{-1}(j)\big|\le\Big\lceil\frac nq\Big\rceil .$$
--
--   In words: no matter which layered piece the birthday agent picks, the other agents can be split into $q$ groups whose sizes (birthday agent included) differ by at most one, each agent receiving a preferred layered piece. The multi-division is chosen once, before the birthday agent's choice. For $m=1$ and $q=n$ this recovers the Avvakumov–Karasev theorem on envy-free division without hungry agents.
--
--   **Formalization Note.** Agents are `Fin n`, the birthday agent an arbitrary `b : Fin n` (the page labels it $n$, without loss of generality). "Prime power" is `IsPrimePow q`, which excludes $q=1$. The group sizes count all $n$ agents, as the page's "including the birthday agent" asks; $\{\lfloor n/q\rfloor,\lceil n/q\rceil\}$ is written as the two inequalities, which is equivalent. Every agent, the birthday agent included, has closed preferences, as on the page. The model's definitions, including the reading that a choice function prefers at least one entry of each multi-division, are in `MultiLayerCake.LongKnives.Model`.
-- source:
--   Igarashi, Meunier, Envy-Free Division of Multi-Layered Cakes, arXiv:2106.02262v4, p. 5, Theorem 1

import Mathlib
import Definitions.Def_MultiLayerCake_LongKnives_Model

namespace MultiLayerCake.LongKnives

/-- Theorem 1, p. 5 (formal version, same page): for `m ≤ q ≤ n` with `q` a prime power and agents
with closed preferences, there is a feasible and contiguous multi-division `A` into `q` layered
pieces, obtained with `q − 1` long knives, such that for every choice `jStar` of the birthday agent
`b` there is an assignment `π` with `π b = jStar`, every other agent assigned to a preferred layered
piece, and every layered piece receiving between `⌊n/q⌋` and `⌈n/q⌉` agents (birthday agent
included). -/
theorem theorem_1 {m n q : ℕ} (hmq : m ≤ q) (hqn : q ≤ n) (hq : IsPrimePow q)
    (c : Fin n → (Fin q → Fin m → Set ℝ) → Set (Fin m → Set ℝ))
    (hc : ∀ i, IsChoiceFunction (c i)) (hcl : ∀ i, ClosedPreferences (c i)) (b : Fin n) :
    ∃ A : Fin q → Fin m → Set ℝ, IsMultiDivision A ∧ IsContiguous A ∧ IsFeasible A ∧
      ByLongKnives A ∧
      ∀ jStar : Fin q, ∃ π : Fin n → Fin q, π b = jStar ∧ (∀ i, i ≠ b → A (π i) ∈ c i A) ∧
        ∀ j, n / q ≤ (Finset.univ.filter (fun i => π i = j)).card ∧
          (Finset.univ.filter (fun i => π i = j)).card ≤ ⌈(n : ℚ) / q⌉₊ := by sorry

end MultiLayerCake.LongKnives
