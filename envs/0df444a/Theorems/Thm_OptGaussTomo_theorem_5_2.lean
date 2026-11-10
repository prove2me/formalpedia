-- Prove2me | Theorems.Thm_OptGaussTomo_theorem_5_2
-- name    : OptGaussTomo.theorem_5_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T04:08:11.646382+00:00
-- url     : https://prove2.me/theorems/f82a7dfb-d109-4a58-bb10-f0b459b56f5a
-- title:
--   Theorem 5.2 — bosonic Gaussian tomography lower bound $\Omega((m^2+\log\delta^{-1})/\varepsilon^2)$
-- statement:
--   There are universal constants $c,\varepsilon_0,\delta_0>0$ such that for every $m\ge1$, $0<\varepsilon\le\varepsilon_0$ and $0<\delta\le\delta_0$: if some measurement on $n$ copies outputs, for every $m$-mode pure bosonic Gaussian state $\psi$, an estimate $\hat\psi$ with $P(\psi,\hat\psi)\le\varepsilon$ with probability at least $1-\delta$, then
--
--   $$
--   n\ \ge\ c\,\frac{m^2+\log(\delta^{-1})}{\varepsilon^2}.
--   $$
--
--   Hence the protocol of Theorem 5.1 is optimal, already for pure states.
--
--   Differences from the source:
--   - reading: Ω((m² + log(δ⁻¹))/ε²) copies → universal constants c, ε₀, δ₀ > 0 fixed before m, ε, δ; for 0 < ε ≤ ε₀ and 0 < δ ≤ δ₀ every successful n satisfies n ≥ c(m² + log δ⁻¹)/ε²; reason: a lower bound containing log δ⁻¹ can hold only for small ε, δ (for δ ≥ 1 zero copies succeed); the proofs use success probability 0.99 and k = ⌊1/(4ε²)⌋
--   - reading: outputs an estimate ψ̂ → the estimate is an arbitrary density operator; reason: the stronger lower bound; the paper takes a pure Gaussian estimate without loss of generality (p.40)
--   - encoding: a tomography protocol using n copies → an n-copy POVM with density-operator outcomes, fixed before the unknown state (Learns); reason: any measurement with classical post-processing is such a POVM; the protocol may not depend on the state
-- source:
--   Chen, Fanizza, Girardi, Lami, Mele, Walter, Witteveen, Optimal tomography of bosonic and fermionic Gaussian states, arXiv:2607.11847 (held version, sha256 0f7548a2a5cfd55079e5d7f1787c97c8561a818a53d7e29824715104bad416ed), Theorem 5.2 p.14 (pdf p.14)

import Mathlib
import Definitions.Def_OptGaussTomo_Learns
import Definitions.Def_OptGaussTomo_purifiedDist
import Definitions.Def_OptGaussTomo_boseGauss

namespace OptGaussTomo

/-- **Theorem 5.2** (Bosonic Gaussian tomography, lower bound; Chen, Fanizza, Girardi, Lami, Mele,
Walter, Witteveen, *Optimal tomography of bosonic and fermionic Gaussian states*, arXiv:2607.11847,
held version, sha256 0f7548a2…, Theorem 5.2, p.14). Suppose there exists a tomography protocol for
`m`-mode pure bosonic Gaussian states `ψ` that outputs an estimate `ψ̂` with purified distance at
most `P(ψ, ψ̂) ≤ ε` with probability at least `1 − δ` for any pure Gaussian state. Then this
protocol needs to use at least `Ω((m² + log(δ⁻¹))/ε²)` copies of `ψ`.

**Formalization Note.** `Ω(·)` is read with universal constants `c, ε₀, δ₀ > 0`, fixed before
`m ≥ 1`, `ε`, `δ`: for `0 < ε ≤ ε₀`, `0 < δ ≤ δ₀`, every successful `n` satisfies
`n ≥ c (m² + log δ⁻¹)/ε²` (a lower bound with a `log δ⁻¹` term can hold only for small `δ`). The
estimate is an arbitrary state (a stronger lower bound than for pure estimates). The class
`bosePure m` is every pure bosonic Gaussian state, any mean, no energy bound. `log` is natural. -/
theorem theorem_5_2 :
    ∃ c ε₀ δ₀ : ℝ, 0 < c ∧ 0 < ε₀ ∧ 0 < δ₀ ∧
      ∀ m : ℕ, 1 ≤ m → ∀ ε δ : ℝ, 0 < ε → ε ≤ ε₀ → 0 < δ → δ ≤ δ₀ → ∀ n : ℕ,
        Learns (bosePure m) purifiedDist n ε δ →
          c * (((m : ℝ) ^ 2 + Real.log δ⁻¹) / ε ^ 2) ≤ n := by sorry

end OptGaussTomo
