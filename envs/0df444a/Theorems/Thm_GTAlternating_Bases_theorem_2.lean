-- Prove2me | Theorems.Thm_GTAlternating_Bases_theorem_2
-- name    : GTAlternating.Bases.theorem_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T17:28:19.181013+00:00
-- url     : https://prove2.me/theorems/15d0aa2e-e43b-44c3-a619-000f67c50820
-- title:
--   Theorem 2, p. 10 — branching rule A_n ↓ A_{n−1}: V_β ⊏ V_α unless both are self-conjugate with opposite signs
-- statement:
--   For a representation $W$ of $A_{n-1}$ and a representation $V$ of $A_n$, write $W \sqsubset V$ if $W$ occurs in the restriction of $V$ to $A_{n-1}$. Let $n \ge 3$, $\alpha \in \tilde\Theta(n)$ with partition $\lambda$ and $\beta \in \tilde\Theta(n-1)$ with partition $\mu$, such that $\mu \in \lambda^{\downarrow}$ or $\mu' \in \lambda^{\downarrow}$. Then
--   $$V_\beta \sqsubset V_\alpha \iff \text{not } (\alpha = \lambda^{s},\ \beta = \mu^{t} \text{ with } s \ne t).$$
--   Equivalently, the relation is given by the table
--
--   | | $\lambda \ne \lambda'$ | $\lambda = \lambda'$ |
--   |---|---|---|
--   | $\mu \ne \mu'$ | $V_\mu \sqsubset V_\lambda$ | $V_\mu \sqsubset V_\lambda^{+}$, $V_\mu \sqsubset V_\lambda^{-}$ |
--   | $\mu = \mu'$ | $V_\mu^{+} \sqsubset V_\lambda$, $V_\mu^{-} \sqsubset V_\lambda$ | $V_\mu^{+} \sqsubset V_\lambda^{+}$, $V_\mu^{-} \sqsubset V_\lambda^{-}$ |
--
--   with no other occurrences ($V_\mu^{\pm} \not\sqsubset V_\lambda^{\mp}$).
--
--   This is the branching rule of the alternating tower; it is what makes the paths $\tilde{\mathcal S}(\alpha)$ the geodesics of its Bratteli diagram.
--
--   **Formalization Note.** $V_\beta \sqsubset V_\alpha$ is: the $A_{n-1}$-isotypic subspace of type $V_\beta$ inside $V_{\mathrm{shape}(\alpha)}$ meets $V_\alpha$ nontrivially. The negative entries ($V_\mu^{\pm} \not\sqsubset V_\lambda^{\mp}$) are the paper's "determined by the table": exactly the listed occurrences hold. $n \ge 3$ so that $A_{n-1}$ has $n-1 \ge 2$. $A_k$-equivariance is commutation with the generators $s_is_j$.
-- source:
--   Geetha, Prasad, Comparison of Gelfand-Tsetlin bases for alternating and symmetric groups, arXiv:1606.04424v2, p. 10, Theorem 2

import Mathlib
import Definitions.Def_GTAlternating_Bases_Model

namespace GTAlternating.Bases

open QAlgorithms.Papers.Independent.Renew46.P26

theorem theorem_2 (a b : Label) (ha : 3 ≤ a.size)
    (hab : YoungEdge b.shape a.shape ∨ YoungEdge b.shape.transpose a.shape) :
    Occurs b a ↔
      ¬ ∃ (lam mu : YoungDiagram) (hl : lam.transpose = lam) (hm : mu.transpose = mu) (s t : Bool),
          a = .sc lam hl s ∧ b = .sc mu hm t ∧ s ≠ t := by sorry

end GTAlternating.Bases
