-- Prove2me | Theorems.Thm_HermiteLaptop_MaxAgree_eq_10_11
-- name    : HermiteLaptop.MaxAgree.eq_10_11
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T18:17:21.972478+00:00
-- url     : https://prove2.me/theorems/76e0df12-e81f-4f3b-b953-f9f81315d566
-- title:
--   §2.3, Eqs. (10)–(11) — P_k(0) = c_{k,0} = 1/k and P_k(1) = Σ_m c_{k,m} = 1
-- statement:
--   Fix $k\ge1$. At $\rho=0$ the two Gaussian vectors are independent and the argmax indices are uniform on $[k]$; at $\rho=1$ they coincide. Accordingly
--   $$P_k(0)=c_{k,0}=\frac1k,\qquad P_k(1)=\sum_{m=0}^{\infty}c_{k,m}=1 .$$
--   Equation (10) gives the negative-edge value of the 4/5-spokes mixture at $\rho=0$, and (11) is the normalization used in Lemma 2.1 and Proposition 2.4.
--
--   **Formalization Note.** $\sum_m c_{k,m}=1$ is stated as `HasSum (fun m => coeffC k m) 1`.
--
--   Differences from the source:
--   - encoding: Σ_{m=0}^∞ c_{k,m} = 1 → HasSum (coeffC k) 1; reason: convergence asserted, no junk tsum
-- source:
--   García-Soriano, Miyauchi, Hermite Brings a Laptop, arXiv:2609.35453 (held version, sha256 97504f90…), p. 14 (PDF 17), §2.3, Eqs. (10)–(11)

import Mathlib
import Definitions.Def_HermiteLaptop_MaxAgree_Hermite

namespace HermiteLaptop.MaxAgree

/-- §2.3, Eqs. (10)–(11): `P_k(0) = c_{k,0} = 1/k` and `P_k(1) = Σ_m c_{k,m} = 1`. -/
theorem eq_10_11 (k : ℕ) (hk : 1 ≤ k) :
    collisionProb k 0 = 1 / (k : ℝ) ∧ coeffC k 0 = 1 / (k : ℝ) ∧
    collisionProb k 1 = 1 ∧ HasSum (fun m : ℕ => coeffC k m) 1 := by sorry

end HermiteLaptop.MaxAgree
