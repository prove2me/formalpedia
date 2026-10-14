-- Prove2me | Theorems.Thm_IntMul_HvdH_prop_4_7_ii
-- name    : IntMul.HvdH.prop_4_7_ii
-- status  : Proved
-- author  : @xuanji
-- created : 2026-10-12T00:39:23.196421+00:00
-- url     : https://prove2.me/theorems/257f07e8-335f-4c87-ab83-95b51baf7023
-- title:
--   Gaussian resampling in one dimension with computable approximations (Proposition 4.7)
-- statement:
--   Let $s<t$ be coprime positive integers. Let $\alpha\ge2$ and $p$ be integers with $\alpha^2\le p$ and $\alpha^2\theta\ge1$, where $\theta=t/s-1$, i.e. $s\le\alpha^2(t-s)$. Let $n$ = `jIter p s t α` and $m$ = `eWidth p α`, and assume $100(n(10m+12)+1)\le2^p$.
--
--   Then there are linear maps $\mathcal A:\mathbb C^s\to\mathbb C^t$ and $\mathcal B:\mathbb C^t\to\mathbb C^s$ with the following properties.
--   * $\|\mathcal A\|,\|\mathcal B\|\le1$ in the sup norm.
--   * $$F_s=2^{2\alpha^2}\,\mathcal BF_t\mathcal A,$$ where $F_n=n^{-1}\cdot$`ZMod.dft` is the normalised DFT.
--   * The computable maps `Sapprox` (Lemma 4.9) and `Bapprox` (`IntMul_HvdH_BApprox`) approximate $\mathcal A$ and $\mathcal B$ on fixed-point vectors. For $U\in\mathbb Z[i]^s$ and $V\in\mathbb Z[i]^t$ with entries of modulus at most $2^p$:
--   $$|\mathrm{Sapprox}(U)_k-2^p(\mathcal A\,2^{-p}U)_k|\le6\lceil\sqrt p\rceil\alpha+4,$$
--   $$|\mathrm{Bapprox}(V)_j-2^p(\mathcal B\,2^{-p}V)_j|\le n(10m+12)+4.$$
--
--   This is Proposition 4.7 of Harvey–van der Hoeven, with explicit $\mathcal A=\mathcal S/2$ and $\mathcal B=P_s^{-1}\mathcal D'\mathcal J'\mathcal CP_t$, and both parts (i) and (ii) in one statement. Both error bounds are $O(p^{3/2})$ under the hypotheses. The paper's bound is $p^2$.
-- source:
--   Harvey, van der Hoeven, Integer multiplication in time O(n log n), Annals of Math. 193 (2021), https://hal.science/hal-02070778, Proposition 4.7

import Mathlib
import Definitions.Def_IntMul_HvdH_BApprox
import Theorems.Thm_IntMul_HvdH_Sapprox_bound
import Theorems.Thm_IntMul_HvdH_Dapprox_bound
import Theorems.Thm_IntMul_HvdH_Japprox_bound

namespace IntMul.HvdH
theorem prop_4_7_ii (p s t α : ℕ) [NeZero s] [NeZero t] (hst : s < t) (hcop : Nat.Coprime s t)
    (hα : 2 ≤ α) (hαp : α ^ 2 ≤ p) (hx : s ≤ α ^ 2 * (t - s))
    (hp : 100 * (jIter p s t α * (10 * eWidth p α + 12) + 1) ≤ 2 ^ p) :
    ∃ (A : (ZMod s → ℂ) →L[ℂ] (ZMod t → ℂ)) (B : (ZMod t → ℂ) →L[ℂ] (ZMod s → ℂ)),
      ‖A‖ ≤ 1 ∧ ‖B‖ ≤ 1 ∧
      (∀ u, (s : ℂ)⁻¹ • ZMod.dft u = (2 : ℂ) ^ (2 * α ^ 2) • B ((t : ℂ)⁻¹ • ZMod.dft (A u))) ∧
      (∀ U : ℕ → ℤ × ℤ, (∀ i, ‖((U i).1 : ℂ) + ((U i).2 : ℂ) * Complex.I‖ ≤ 2 ^ p) → ∀ k : ZMod t,
        ‖(((Sapprox p s t α U k.val).1 : ℂ) + ((Sapprox p s t α U k.val).2 : ℂ) * Complex.I) -
          2 ^ p * A (fun j => (((U j.val).1 : ℂ) + ((U j.val).2 : ℂ) * Complex.I) / 2 ^ p) k‖
          ≤ 6 * sWidth p α + 4) ∧
      (∀ V : ℕ → ℤ × ℤ, (∀ i, ‖((V i).1 : ℂ) + ((V i).2 : ℂ) * Complex.I‖ ≤ 2 ^ p) → ∀ j : ZMod s,
        ‖(((Bapprox p s t α V j.val).1 : ℂ) + ((Bapprox p s t α V j.val).2 : ℂ) * Complex.I) -
          2 ^ p * B (fun k => (((V k.val).1 : ℂ) + ((V k.val).2 : ℂ) * Complex.I) / 2 ^ p) j‖
          ≤ jIter p s t α * (10 * eWidth p α + 12) + 4) := by sorry
end IntMul.HvdH
