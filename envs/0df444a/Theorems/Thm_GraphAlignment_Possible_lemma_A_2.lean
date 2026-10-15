-- Prove2me | Theorems.Thm_GraphAlignment_Possible_lemma_A_2
-- name    : GraphAlignment.Possible.lemma_A_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T02:31:13.248255+00:00
-- url     : https://prove2.me/theorems/c12a0129-ce26-4e93-b2f8-a22e391abf86
-- title:
--   Lemma A.2 (In particular), p. 21 — ψ_{λ/2−1}(2λ/3) ≥ 0.7 for λ ≥ 20
-- statement:
--   Let $\psi_j(\mu) = \mathbb P(\mathrm{Po}(\mu) \ge j)$ be the tail of a Poisson random variable with parameter $\mu$. For every real $\lambda \ge 20$,
--   $$\psi_{\lambda/2 - 1}\Big(\frac{2\lambda}{3}\Big) \ge 0.7 .$$
--
--   A Poisson variable with mean $2\lambda/3$ exceeds $\lambda/2 - 1$ with probability at least $0.7$; the paper uses it to locate the $k$-core parameter in its proof of Proposition 4.2.
--
--   **Formalization Note** Only the "In particular" part of Lemma A.2 is stated. The general normal-approximation bound $\psi_j(\mu) \ge 1 - \phi((j-\mu)/\sqrt\mu) - 0.55/\sqrt{\lceil\mu\rceil}$ is not stated, because the paper's proof of it does not hold as written (it uses $\mathbb E|X_i|^3 = \mu/\lceil\mu\rceil$ and an unnormalised Berry–Esseen constant). The threshold $\lambda/2 - 1$ is a real number, as in the paper's application.
-- source:
--   Hall, Massoulié, Partial Recovery in the Graph Alignment Problem, arXiv:2007.00533v5, p. 21, Lemma A.2 ("In particular")

import Mathlib
import Definitions.Def_GraphAlignment_Possible_PoissonTail

namespace GraphAlignment.Possible

theorem lemma_A_2 (lam : ℝ) (hlam : 20 ≤ lam) :
    (0.7 : ℝ) ≤ psi (lam / 2 - 1) (2 * lam / 3) := by sorry

end GraphAlignment.Possible
