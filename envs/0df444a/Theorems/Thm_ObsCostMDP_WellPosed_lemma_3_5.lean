-- Prove2me | Theorems.Thm_ObsCostMDP_WellPosed_lemma_3_5
-- name    : ObsCostMDP.WellPosed.lemma_3_5
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-13T20:51:44.062123+00:00
-- url     : https://prove2.me/theorems/b94afc9e-2294-4ef9-9ddf-6fb99ea6e0bf
-- title:
--   Lemma 3.5 — the restriction of F to {1, …, N} satisfies the monotonicity property (3.5) with the same β
-- statement:
--   Let $X$, $A$ be finite and nonempty and let $F$ be a driver of Problem 3.1 satisfying Assumption 3.2 with constant $\beta>0$. Fix $N\in\mathbb N$ and let $\tilde F$ be the restriction of $F$ to the time set $\{1,\dots,N\}$, $\tilde F_a(u)^n_x=F_a(n,x,u(n,x),u_a)$, where $u_a$ is extended by $0$ outside $\{1,\dots,N\}$. Then for all $u,v\in\mathbb R^{N\times L\times d}$ and every index $(\bar n,\bar a,\bar l)$ with $u^{\bar n}_{\bar a,\bar l}-v^{\bar n}_{\bar a,\bar l}=\max_{n,a,l}(u^n_{a,l}-v^n_{a,l})\ge0$,
--
--   $$\tilde F_{\bar a}(u)^{\bar n}_{\bar l}-\tilde F_{\bar a}(v)^{\bar n}_{\bar l}\ge\beta\big(u^{\bar n}_{\bar a,\bar l}-v^{\bar n}_{\bar a,\bar l}\big).$$
--
--   This reduces the monotonicity condition of the infinite problem to the finite-dimensional property (3.5) on which the comparison principles for the truncated and penalised problems rest.
--
--   **Formalization Note** Lemma 3.5 also asserts that $\tilde F_a$ is continuous; the paper's proof shows only (3.5), and that clause is not part of this statement. The constant of (3.5) is the $\beta$ of Assumption 3.2. The extension by $0$ also covers time $0$.
-- source:
--   Reisinger & Tam, Markov decision processes with observation costs: framework and computation with a penalty scheme, arXiv:2201.07908v3, p. 17, Lemma 3.5

import Mathlib
import Definitions.Def_ObsCostMDP_WellPosed_QVI
import Definitions.Def_ObsCostMDP_WellPosed_Truncated

namespace ObsCostMDP.WellPosed

/-- **Lemma 3.5** (Reisinger–Tam, arXiv:2201.07908v3, p. 17), monotonicity part. If `F` satisfies
Assumption 3.2 with constant `β`, then its restriction `F̃` to `{1, …, N}` satisfies property (3.5)
with the same constant `β`.
**Formalization Note**: the restriction evaluates the function argument `u_a` on the zero extension
of the truncated `u_a` (zero at time `0` and at times `> N`), the convention of Theorem 3.13.
The continuity of `F̃` asserted in the lemma is not part of this statement (the paper's proof
does not address it). -/
theorem lemma_3_5 {X A : Type*} [Fintype X] [DecidableEq X] [Nonempty X]
    [Fintype A] [DecidableEq A] [Nonempty A]
    (F : Driver X A) (β : ℝ) (hF : Assumption32 F β) (N : ℕ) :
    Property35 (restrictDriver F N) β := by sorry

end ObsCostMDP.WellPosed
