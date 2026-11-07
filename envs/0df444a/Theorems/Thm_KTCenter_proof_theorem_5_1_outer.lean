-- Prove2me | Theorems.Thm_KTCenter_proof_theorem_5_1_outer
-- name    : KTCenter.proof_theorem_5_1_outer
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T11:31:02.169821+00:00
-- url     : https://prove2.me/theorems/4fe6c649-142c-4e02-8b77-6669bb4da274
-- title:
--   Proof of Theorem 5.1, (72)–(74) — the outer error calculation, also used by Corollary 6.4
-- statement:
--   Relabel so that $\rho=\pi_1=(1,\dots,d)$. Let $\varepsilon>0$, let $\varepsilon_0$ be rational with $0<\varepsilon_0\le\min\{\varepsilon,1/2\}$, and set (15): $\delta=\varepsilon_0/8$, $r=1+\lceil1/\delta\rceil$, $\beta=\zeta=\xi=\varepsilon_0/(160r)$. Let $J\ni1$ with $|J|\le r$ and a ranking $\tau$ satisfy (9) with $w_v=5\deg_{E_J}(v)$. Then:
--
--   1. if $W=0$, then $\tau=\rho$ and $\mathrm{Obj}(\Pi,\rho)\le(1+\varepsilon)R^*$;
--   2. if $W>0$, then $W\ge1$; some allowed $p_0$ satisfies (72)
--   $$\min_{p}\max_i\tilde C_i(p)\le\max_i\tilde C_i(p_0)\le\mathrm{Obj}(\Pi,\sigma_{p_0})\le(1+2\delta)R^*+2\beta W;$$
--   every allowed $p$ with $\max_i\tilde C_i(p)\le\min_q\max_i\tilde C_i(q)+\xi W$ satisfies (73)
--   $$\mathrm{Obj}(\Pi,\sigma_p)\le\max_i\tilde C_i(p)+\zeta W\le(1+2\delta)R^*+(2\beta+\zeta+\xi)W;$$
--   and (74): $(1+2\delta)R^*+(2\beta+\zeta+\xi)W\le(1+3\varepsilon_0/4)R^*\le(1+\varepsilon)R^*$.
--
--   Differences from the source:
--
--   - encoding: candidates relabeled by their position in the first input, so ρ = π₁ = (1, …, d) (§4.1) → hypothesis `I.π I.first = 1` on the input list; reason: the relabeling preserves all distances and is undone at the end (p.17); the statements of §§4–5 are about relabeled inputs
--   - reading: p returned by Algorithm 9 with guarantee (70) (Theorem 5.1), or by Theorem 6.1 (Corollary 6.4) → every allowed p satisfying (75) with additive ξW; reason: both guarantees are this inequality
-- source:
--   Chakraborty, Das, Mukherjee, Kendall–tau Center Admits a PTAS, STOC 2027 submission (manuscript sha256 4739ffba…), Proof of Theorem 5.1, eqs. (72)–(74), pp.56–57 (PDF pp.58–59); Corollary 6.4, p.65 (PDF p.67)

import Mathlib
import Definitions.Def_KTCenter_Instance
import Definitions.Def_KTCenter_InversionUnion
import Definitions.Def_KTCenter_KeyDomains
import Definitions.Def_KTCenter_PartitionCosts

namespace KTCenter

/-- **Proof of Theorem 5.1, (72)–(74)**, pp.56–57 (PDF pp.58–59); the same calculation in the proof of
Corollary 6.4, p.65.

Chakraborty, Das, Mukherjee, *Kendall–tau Center Admits a PTAS*, STOC 2027 submission (manuscript
sha256 4739ffba…).

**Formalization Note.** Parameters (15) with rational `ε₀`, `0 < ε₀ ≤ min{ε, 1/2}`: `δ = ε₀/8`,
`r = 1 + ⌈1/δ⌉`, `β = ζ = ξ = ε₀/(160r)`. On relabeled inputs, `π₁ = 1`. `J` and `τ` are as in (9), so
`w_v` is the allowance of `J`. "`p` with (75)" replaces the reference to Algorithm 9's guarantee (70):
the corollary's proof uses the same additive `ξW`. -/
theorem proof_theorem_5_1_outer (I : Instance) (hρ : I.π I.first = 1) (ε : ℝ) (ε₀ : ℚ) (hε₀ : 0 < ε₀)
    (hε₀ε : (ε₀ : ℝ) ≤ ε) (hε₀2 : ε₀ ≤ 1 / 2) (r : ℕ) (hr : r = 1 + ⌈1 / (ε₀ / 8)⌉₊)
    (β : ℚ) (hβ : β = ε₀ / (160 * (r : ℚ))) (J : Finset (Fin I.n)) (hJ : I.first ∈ J)
    (hJr : J.card ≤ r) (τ : Equiv.Perm (Fin I.d))
    (hτobj : (obj I τ : ℝ) ≤ (1 + 2 * ((ε₀ : ℝ) / 8)) * (optRadius I : ℝ))
    (hτw : ∀ v, |lab (τ⁻¹ v) - lab v| ≤ (allowance I J v : ℤ)) :
    (totalW (allowance I J) = 0 → τ = 1 ∧ (obj I 1 : ℝ) ≤ (1 + ε) * (optRadius I : ℝ)) ∧
    (0 < totalW (allowance I J) →
      1 ≤ totalW (allowance I J) ∧
      (∃ p₀ ∈ assignments (allowance I J) β,
        PartitionCosts.minMaxSurrogate I (allowance I J) β β ≤
          PartitionCosts.maxSurrogate I (allowance I J) β β p₀ ∧
        PartitionCosts.maxSurrogate I (allowance I J) β β p₀ ≤ obj I (sortRanking p₀) ∧
        (obj I (sortRanking p₀) : ℝ) ≤ (1 + 2 * ((ε₀ : ℝ) / 8)) * (optRadius I : ℝ) +
          2 * (β : ℝ) * (totalW (allowance I J) : ℝ)) ∧
      (∀ p ∈ assignments (allowance I J) β,
        (PartitionCosts.maxSurrogate I (allowance I J) β β p : ℚ) ≤
          (PartitionCosts.minMaxSurrogate I (allowance I J) β β : ℚ) +
            β * (totalW (allowance I J) : ℚ) →
        (obj I (sortRanking p) : ℝ) ≤ (PartitionCosts.maxSurrogate I (allowance I J) β β p : ℝ) +
            (β : ℝ) * (totalW (allowance I J) : ℝ) ∧
        (PartitionCosts.maxSurrogate I (allowance I J) β β p : ℝ) +
            (β : ℝ) * (totalW (allowance I J) : ℝ) ≤
          (1 + 2 * ((ε₀ : ℝ) / 8)) * (optRadius I : ℝ) +
            (2 * (β : ℝ) + β + β) * (totalW (allowance I J) : ℝ)) ∧
      (1 + 2 * ((ε₀ : ℝ) / 8)) * (optRadius I : ℝ) +
          (2 * (β : ℝ) + β + β) * (totalW (allowance I J) : ℝ) ≤
        (1 + 3 * (ε₀ : ℝ) / 4) * (optRadius I : ℝ) ∧
      (1 + 3 * (ε₀ : ℝ) / 4) * (optRadius I : ℝ) ≤ (1 + ε) * (optRadius I : ℝ)) := by sorry

end KTCenter
