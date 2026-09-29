-- Prove2me | Theorems.Thm_JacksonJobshop_Equilibrium_product_form_is_distribution
-- name    : JacksonJobshop.Equilibrium.product_form_is_distribution
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T15:13:50.2641+00:00
-- url     : https://prove2.me/theorems/4463f439-bc3a-4e93-a1e8-fc5aaf0ae34f
-- title:
--   §4, proof of Theorem (4.5), first claim — (4.6) defines a probability distribution
-- statement:
--   Let $(N, L, M, R)$ be a jobshop-like queueing system satisfying Assumptions (2.1)–(2.4), with the notations $W$, $w$, $\pi$ of (4.1)–(4.4). If $\pi > 0$, then
--   $$p(\bar k) = \pi\, w(\bar k)\, W(S(\bar k)) \tag{4.6}$$
--   defines a probability distribution over state vectors $\bar k \in \mathbb{Z}_{\ge 0}^N$: every $p(\bar k) \ge 0$ and
--   $$\sum_{\bar k} p(\bar k) = 1.$$
--
--   This is the first of the two verifications the paper names as the proof of Theorem (4.5).
--
--   **Formalization Note** The sum over state vectors is an unconditional sum (`HasSum`) over `Fin N → ℕ`.
-- source:
--   Jackson, Jobshop-Like Queueing Systems, Management Science 10(1) (1963), p. 136, §4, sentence before Theorem (4.5), first claim

import Mathlib
import Definitions.Def_JacksonJobshop_Equilibrium_System

namespace JacksonJobshop.Equilibrium

/-- Jackson (1963), p. 136, first claim of the proof sentence before Theorem (4.5): if `π > 0`,
then (4.6) `p(k) = π w(k) W(S(k))` defines a probability distribution over state vectors. -/
theorem product_form_is_distribution {N : ℕ} (sys : JobshopSystem N) (hπ : 0 < piConst sys) :
    (∀ k, 0 ≤ productForm sys k) ∧ HasSum (productForm sys) 1 := by sorry

end JacksonJobshop.Equilibrium
