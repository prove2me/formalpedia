-- Prove2me | Theorems.Thm_JacksonJobshop_Equilibrium_product_form_satisfies_balance
-- name    : JacksonJobshop.Equilibrium.product_form_satisfies_balance
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-27T15:14:15.20718+00:00
-- url     : https://prove2.me/theorems/07003402-33c2-4f44-b82d-7797a9af28ec
-- title:
--   §4, proof of Theorem (4.5), second claim — (4.6) satisfies equations (3.1)
-- statement:
--   Let $(N, L, M, R)$ be a jobshop-like queueing system satisfying Assumptions (2.1)–(2.4), and let $p(\bar k) = \pi\, w(\bar k)\, W(S(\bar k))$ be the function (4.6). Then $P(\bar k, t) \equiv p(\bar k)$ is a constant solution of the balance equations (3.1): for every state vector $\bar k$,
--   $$0 = -\Big[\lambda(S(\bar k))\sum_{n=1}^N r(0, n) + \sum_{n} \mu(n, k_n)\big(1 - r(n, n)\big)\Big] p(\bar k) + \sum_n \lambda(S(\bar k) - 1)\, r(0, n)\, p(\bar h(n)) + \sum_n \mu(n, k_n + 1)\, r(n, N+1)\, p(\bar l(n)) + \sum_{m \ne n} \mu(n, k_n + 1)\, r(n, m)\, p(\bar j(m, n)),$$
--   with the conventions of (3.1): sums over $[1, N]$, terms whose state argument has a negative component omitted.
--
--   This is the second verification the paper names as the proof of Theorem (4.5), and the substantive one.
--
--   **Formalization Note** The paper prints $\lambda(S(\bar k))$ as the arrival-outflow coefficient in (3.1); this is inconsistent with its own transition probabilities on p. 134 whenever $r(0, N+1) > 0$, and we use $\lambda(S(\bar k)) \sum_n r(0, n)$, which is the equation those transition probabilities give. With the printed coefficient the claim is false (e.g. $N = 1$, $r(0,1) = r(0,2) = 1/2$, $r(1,2) = 1$, constant rates, at $\bar k = 0$). The statement carries no hypothesis on $\pi$: the equations are linear in $p$.
-- source:
--   Jackson, Jobshop-Like Queueing Systems, Management Science 10(1) (1963), p. 136, §4, sentence before Theorem (4.5), second claim; equations (3.1), p. 135

import Mathlib
import Definitions.Def_JacksonJobshop_Equilibrium_System

namespace JacksonJobshop.Equilibrium

/-- Jackson (1963), p. 136, second claim of the proof sentence before Theorem (4.5): the
function (4.6) `p(k) = π w(k) W(S(k))` satisfies the stationary equations (3.1) (with the
arrival-outflow coefficient `λ(S(k)) Σ_n r(0, n)`) at every state vector. -/
theorem product_form_satisfies_balance {N : ℕ} (sys : JobshopSystem N) :
    ∀ k, Balance sys (productForm sys) k := by sorry

end JacksonJobshop.Equilibrium
