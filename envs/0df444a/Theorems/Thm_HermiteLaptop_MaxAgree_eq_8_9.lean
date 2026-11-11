-- Prove2me | Theorems.Thm_HermiteLaptop_MaxAgree_eq_8_9
-- name    : HermiteLaptop.MaxAgree.eq_8_9
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T18:17:23.724217+00:00
-- url     : https://prove2.me/theorems/dbd2ca16-9798-4019-8b99-ef3333de07be
-- title:
--   §2.3, Eqs. (8)–(9) — Hermite power series P_k(ρ) = Σ_m c_{k,m} ρ^m with c_{k,m} = k W_m(f_1) ≥ 0
-- statement:
--   Fix $k\ge1$. For every $\rho\in[-1,1]$ the collision probability of the $k$-spokes rounding has the Hermite power-series expansion
--   $$P_k(\rho)=\sum_{p=1}^{k}\sum_{m=0}^{\infty}\rho^mW_m(f_p)=\sum_{m=0}^{\infty}c_{k,m}\rho^m,$$
--   each inner series converging, and for every $m\in\mathbb N_0$
--   $$c_{k,m}=\sum_{p=1}^kW_m(f_p)=kW_m(f_1)=k\sum_{|\alpha|=m}\hat f_1(\alpha)^2\ge0.$$
--   Here $f_p$ is the indicator of the argmax region $A_p$ and $W_m$ the level-$m$ Hermite weight. This expansion is the basis of the whole certification framework: monotonicity (Lemma 2.1) and the truncated bounds (Proposition 2.4) are read off from it.
--
--   **Formalization Note.** The series are stated with `Summable`/`tsum` (inner series) and `HasSum` (the expansion of `collisionProb k ρ`), so convergence is part of the claim. $f_1$ is `argmaxRegion ⟨0, hk⟩`.
--
--   Differences from the source:
--   - encoding: the infinite series in (8) → Summable plus tsum for the inner series, HasSum for Σ_m c_{k,m}ρ^m; reason: genuine convergence is asserted, not a junk tsum value
--   - encoding: c_{k,m} defined by (9), W_m(f) by (4) → coeffC k m := Σ_p levelWeight p m with levelWeight p m := Σ_{|α|=m} f̂_p(α)², f_1 = coordinate 0; reason: the defining expressions of (4) and (9); the other equalities of (9) are stated
-- source:
--   García-Soriano, Miyauchi, Hermite Brings a Laptop, arXiv:2609.35453 (held version, sha256 97504f90…), p. 14 (PDF 17), §2.3, Eqs. (8)–(9)

import Mathlib
import Definitions.Def_HermiteLaptop_MaxAgree_Hermite

namespace HermiteLaptop.MaxAgree

/-- §2.3, Eqs. (8)–(9): for `k ≥ 1` and `ρ ∈ [−1, 1]`,
`P_k(ρ) = Σ_p Σ_m ρᵐ W_m(f_p) = Σ_m c_{k,m} ρᵐ`, and `c_{k,m} = k W_m(f_1) ≥ 0`. -/
theorem eq_8_9 (k : ℕ) (hk : 1 ≤ k) :
    (∀ ρ ∈ Set.Icc (-1 : ℝ) 1,
      (∀ p : Fin k, Summable (fun m : ℕ => ρ ^ m * levelWeight p m)) ∧
      collisionProb k ρ = ∑ p : Fin k, ∑' m : ℕ, ρ ^ m * levelWeight p m ∧
      HasSum (fun m : ℕ => coeffC k m * ρ ^ m) (collisionProb k ρ)) ∧
    ∀ m : ℕ, coeffC k m = (k : ℝ) * levelWeight (⟨0, hk⟩ : Fin k) m ∧ 0 ≤ coeffC k m := by sorry

end HermiteLaptop.MaxAgree
