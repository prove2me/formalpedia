-- Prove2me | Theorems.Thm_InventoryControl_lemma_6_1
-- name    : InventoryControl.lemma_6_1
-- status  : Proved
-- author  : @naimengye
-- created : 2026-09-24T00:00:49.97158+00:00
-- url     : https://prove2.me/theorems/2e793919-3aaa-4249-a9c2-0449f49a06ce
-- title:
--   Lemma 6.1: $g(z + xQ)$ is convex in $x$ and minimized at the multiple of $Q$ lying in $\{R+1,\dots,R+Q\}$
-- statement:
--   Let $g$ be the holding-plus-shortage cost rate of a discrete lead-time demand with finite mean,
--   with costs $h > 0$ and $b_1 > 0$, let $Q \ge 1$, let $\bar g(y) = \sum_{j=1}^{Q} g(y+j)$, and
--   let $R$ be an integer minimizing $\bar g$. Then for every integer $z$:
--
--   1. $x \mapsto g(z + xQ)$ is convex on $\mathbb{Z}$, in the sense of nondecreasing increments;
--   2. there is a unique integer $x_z$ with $R + 1 \le z + x_zQ \le R + Q$, and the element
--      $z + x_zQ$ of the band is `reduceToBand R Q z`;
--   3. $g(z + x_zQ) \le g(z + xQ)$ for every integer $x$.
--
--   The proof rests on the telescoping identity (6.21),
--   $g(z + (x+1)Q) - g(z + xQ) = \bar g(z + xQ) - \bar g(z + xQ - 1)$, which is nonpositive while
--   $z + xQ \le R$ and nonnegative once $z + xQ > R + Q$, because $R$ minimizes the convex
--   function $\bar g$. The lemma is the pointwise comparison behind Proposition 6.1: whatever
--   inventory position a policy holds, the position in the band $\{R+1, \dots, R+Q\}$ congruent to
--   it modulo $Q$ costs no more.
--
--   **Formalization Note** Part 2 is stated as three facts about `reduceToBand R Q z`: it lies in
--   the band and differs from $z$ by a multiple of $Q$; uniqueness is immediate from the band's
--   length.
-- source:
--   Sven Axsäter, Inventory Control, 3rd ed., Springer 2015, DOI 10.1007/978-3-319-15729-0, p. 114, Sect. 6.2.1, Lemma 6.1 and its proof, Eq. (6.21)

import Definitions.Def_InventoryControl_rqPolicy

namespace InventoryControl

theorem lemma_6_1 (D : DiscreteDemand) (h b1 : ℝ) (hh : 0 < h) (hb : 0 < b1) (Q : ℕ) (hQ : 0 < Q)
    (R : ℤ) (hR : ∀ y : ℤ, windowCost D h b1 Q R ≤ windowCost D h b1 Q y) (z : ℤ) :
    (∀ x : ℤ, sPolicyCost D h b1 (z + (x + 1) * Q) - sPolicyCost D h b1 (z + x * Q)
        ≤ sPolicyCost D h b1 (z + (x + 2) * Q) - sPolicyCost D h b1 (z + (x + 1) * Q))
      ∧ (R + 1 ≤ reduceToBand R Q z ∧ reduceToBand R Q z ≤ R + Q
          ∧ ∃ x : ℤ, reduceToBand R Q z = z + x * Q)
      ∧ ∀ x : ℤ, sPolicyCost D h b1 (reduceToBand R Q z) ≤ sPolicyCost D h b1 (z + x * Q) := by sorry

end InventoryControl
