-- Prove2me | Theorems.Thm_MarkovChainChoice_SingleResource_value_bellman
-- name    : MarkovChainChoice.SingleResource.value_bellman
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-28T01:18:26.243986+00:00
-- url     : https://prove2.me/theorems/be4dca2f-316c-4cb5-bee6-6067940005fb
-- title:
--   (Single Resource) dynamic program: $V_t(x)$ satisfies the printed recursion and boundary conditions
-- statement:
--   Let $(\lambda,\rho)$ be a Markov chain choice model, $r\in\mathbb R^n$ revenues and $T$ the number of periods. The value functions $V_t(x)$ of the (Single Resource) dynamic program satisfy the boundary conditions $V_{T+1}(x)=0$ for all $x$ and $V_t(0)=0$ for $t=1,\dots,T$, and for $t=1,\dots,T$ and $x\ge 1$,
--   $$V_t(x)=\max_{S\subseteq N}\Big\{\sum_{j\in N}P_{j,S}\{r_j+V_{t+1}(x-1)\}+\Big\{1-\sum_{j\in N}P_{j,S}\Big\}V_{t+1}(x)\Big\}.$$
--
--   This is the first line of the (Single Resource) display: with probability $P_{j,S}$ a customer buys product $j$, earning $r_j$ and leaving $x-1$ units, and otherwise capacity $x$ carries over to period $t+1$. It confirms that the rearranged recursion used to define $V_t$ is the dynamic program as printed.
--
--   **Formalization Note** $V_t(x)$ is `value M r T t x`, defined through the rearranged second line of the display; this theorem states that it satisfies the first line. The maximum is `Finset.sup'` over all subsets of $N$.
-- source:
--   Feldman, Topaloglu, Revenue Management Under the Markov Chain Choice Model, Oper. Res. 65(5), 2017, pp. 1328–1329, Section 5, (Single Resource) and its boundary conditions

import Mathlib
import Definitions.Def_MarkovChainChoice_SingleResource_ValueFunction
open MarkovChainChoice.Shared

namespace MarkovChainChoice.SingleResource

theorem value_bellman {n : ℕ} (M : Model n) (r : Fin n → ℝ) (T : ℕ) :
    (∀ x, value M r T (T + 1) x = 0) ∧
      (∀ t, 1 ≤ t → t ≤ T → value M r T t 0 = 0) ∧
      ∀ t x, 1 ≤ t → t ≤ T → 1 ≤ x →
        value M r T t x =
          (Finset.univ : Finset (Finset (Fin n))).sup' Finset.univ_nonempty (fun S =>
            ∑ j, purchase M S j * (r j + value M r T (t + 1) (x - 1)) +
              (1 - ∑ j, purchase M S j) * value M r T (t + 1) x) := by sorry

end MarkovChainChoice.SingleResource
