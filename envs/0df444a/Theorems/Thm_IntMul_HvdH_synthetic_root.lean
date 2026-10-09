-- Prove2me | Theorems.Thm_IntMul_HvdH_synthetic_root
-- name    : IntMul.HvdH.synthetic_root
-- status  : Proved
-- author  : @avi
-- created : 2026-10-09T01:44:21.35947+00:00
-- url     : https://prove2.me/theorems/e5d4c734-356e-45c2-b041-714d45638be4
-- title:
--   HvdH §2.4 — $y^{2r/n}$ is a principal $n$-th root of unity in $\mathbb C[y]/(y^r+1)$
-- statement:
--   Let $r\ge2$ be a power of two, let $\mathcal R=\mathbb C[y]/(y^r+1)$ with basis $1,y,\dots,y^{r-1}$, and let $n\ge1$ divide $2r$. Then $\omega:=y^{2r/n}$ is a principal $n$-th root of unity in $\mathcal R$:
--
--   1. $\omega^n=1$;
--   2. $\sum_{k=0}^{n-1}(\omega^j)^k=0$ for every $j\ge0$ with $n\nmid j$;
--   3. multiplication by $\omega$ preserves the norm $\|\lambda_0+\lambda_1y+\dots+\lambda_{r-1}y^{r-1}\|=\max_i|\lambda_i|$.
--
--   Formalization note: $\mathcal R$ is `AdjoinRoot (X^r + 1)` over $\mathbb C$, and the coefficients $\lambda_i$ of an element are those of its unique representative of degree $<r$ (`AdjoinRoot.modByMonicHom`). Item 3 is stated as: for every real $B$, all coefficients of $\omega u$ have modulus $\le B$ iff all coefficients of $u$ do, which is equivalent to $\|\omega u\|=\|u\|$. Item 2 uses natural $j$; since $\omega^n=1$ this is equivalent to the paper's condition for all integers $j$.
-- source:
--   D. Harvey, J. van der Hoeven, Integer multiplication in time O(n log n), Ann. of Math. 193 (2021), https://doi.org/10.4007/annals.2021.193.2.4 (preprint https://hal.science/hal-02070778v2), §2.4, synthetic case (2), pp. 12–13 (with the definition of principal root of unity on p. 12 and the norm on R from §2.3).

import Mathlib

namespace IntMul.HvdH

open Polynomial

theorem synthetic_root (r : ℕ) (hr : 2 ≤ r) (hpow : ∃ k : ℕ, r = 2 ^ k) (n : ℕ) (hn : 0 < n)
    (hdiv : n ∣ 2 * r) :
    let hmon : (X ^ r + C (1 : ℂ)).Monic := monic_X_pow_add_C 1 (by omega)
    let ω : AdjoinRoot (X ^ r + C (1 : ℂ)) := AdjoinRoot.root _ ^ (2 * r / n)
    let c : AdjoinRoot (X ^ r + C (1 : ℂ)) → ℕ → ℂ := fun u i =>
      (AdjoinRoot.modByMonicHom hmon u).coeff i
    ω ^ n = 1 ∧
      (∀ j : ℕ, ¬ n ∣ j → ∑ k ∈ Finset.range n, (ω ^ j) ^ k = 0) ∧
      (∀ (u : AdjoinRoot (X ^ r + C (1 : ℂ))) (B : ℝ),
        (∀ i < r, ‖c (ω * u) i‖ ≤ B) ↔ (∀ i < r, ‖c u i‖ ≤ B)) := by sorry

end IntMul.HvdH
