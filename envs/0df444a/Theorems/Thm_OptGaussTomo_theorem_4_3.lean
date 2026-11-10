-- Prove2me | Theorems.Thm_OptGaussTomo_theorem_4_3
-- name    : OptGaussTomo.theorem_4_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T04:08:06.162889+00:00
-- url     : https://prove2.me/theorems/f9e5cb6c-e4e0-4707-b63a-3d835e11d341
-- title:
--   Theorem 4.3 — fermionic Gaussian tomography lower bound $\Omega((m^2+\log\delta^{-1})/\varepsilon^2)$ (corrected: $m\ge2$)
-- statement:
--   There are universal constants $c,\varepsilon_0,\delta_0>0$ such that for every $m\ge2$, $0<\varepsilon\le\varepsilon_0$ and $0<\delta\le\delta_0$: if some measurement on $n$ copies outputs, for every $m$-mode pure fermionic Gaussian state $\psi$, an estimate $\hat\psi$ with purified distance $P(\psi,\hat\psi)\le\varepsilon$ with probability at least $1-\delta$, then
--
--   $$
--   n\ \ge\ c\,\frac{m^2+\log(\delta^{-1})}{\varepsilon^2}.
--   $$
--
--   Hence the protocol of Theorem 4.2 is optimal, already for pure states.
--
--   The statement is false for $m=1$ (see below), which is why it is made for $m\ge2$.
--
--   Differences from the source:
--   - correction: m-mode pure fermionic Gaussian states, every m → m ≥ 2; reason: for m = 1, H₁ = ℂ², every quadratic Hamiltonian (C.2) is a multiple of Z, so the pure Gaussian states are |0⟩ and |1⟩; measuring Z on one copy learns them exactly, so n = 1 succeeds for all ε, δ, contradicting n ≥ c(1 + log δ⁻¹)/ε² as ε → 0 (the paper's own bound n ≥ k(m² − m − 1) − 2m is vacuous at m = 1)
--   - reading: Ω((m² + log(δ⁻¹))/ε²) copies → universal constants c, ε₀, δ₀ > 0 fixed before m, ε, δ; for 0 < ε ≤ ε₀ and 0 < δ ≤ δ₀ every successful n satisfies n ≥ c(m² + log δ⁻¹)/ε²; reason: a lower bound containing log δ⁻¹ can hold only for small ε, δ (for δ ≥ 1 zero copies succeed); the proofs use success probability 0.99 and k = ⌊1/(4ε²)⌋
--   - reading: outputs an estimate ψ̂ → the estimate is an arbitrary density operator; reason: the stronger lower bound; the paper takes a pure Gaussian estimate without loss of generality (p.40)
--   - encoding: a tomography protocol using n copies → an n-copy POVM with density-operator outcomes, fixed before the unknown state (Learns); reason: any measurement with classical post-processing is such a POVM; the protocol may not depend on the state
-- source:
--   Chen, Fanizza, Girardi, Lami, Mele, Walter, Witteveen, Optimal tomography of bosonic and fermionic Gaussian states, arXiv:2607.11847 (held version, sha256 0f7548a2a5cfd55079e5d7f1787c97c8561a818a53d7e29824715104bad416ed), Theorem 4.3 p.12 (pdf p.12)

import Mathlib
import Definitions.Def_OptGaussTomo_Learns
import Definitions.Def_OptGaussTomo_purifiedDist
import Definitions.Def_OptGaussTomo_fermiGauss

namespace OptGaussTomo

/-- **Theorem 4.3** (Fermionic Gaussian tomography, lower bound; corrected: `m ≥ 2`. Chen, Fanizza,
Girardi, Lami, Mele, Walter, Witteveen, *Optimal tomography of bosonic and fermionic Gaussian
states*, arXiv:2607.11847, held version, sha256 0f7548a2…, Theorem 4.3, p.12). Suppose there exists
a tomography protocol for `m`-mode pure fermionic Gaussian states `ψ` that outputs an estimate `ψ̂`
with purified distance at most `P(ψ, ψ̂) ≤ ε` with probability at least `1 − δ` for any pure
Gaussian state. Then this protocol needs to use at least `Ω((m² + log(δ⁻¹))/ε²)` copies of `ψ`.

**Formalization Note.** `Ω(·)` is read with universal constants `c, ε₀, δ₀ > 0`, fixed before `m`,
`ε`, `δ`: for `0 < ε ≤ ε₀`, `0 < δ ≤ δ₀`, every successful `n` satisfies
`n ≥ c (m² + log δ⁻¹)/ε²` (a lower bound with a `log δ⁻¹` term can hold only for small `δ`; for
`δ ≥ 1` a protocol without copies succeeds). The estimate is an arbitrary state (a stronger lower
bound than for pure estimates; the source assumes a pure Gaussian estimate without loss of
generality, p.40). **Correction:** the statement is made for `m ≥ 2`. For `m = 1` it is false:
`H_1 = ℂ²`, every quadratic Hamiltonian (C.2) is a multiple of `Z`, so the pure Gaussian states are
`|0⟩` and `|1⟩` only, and measuring `Z` on one copy learns the state exactly; then `n = 1` succeeds
for every `ε, δ`, contradicting `n ≥ c(1 + log δ⁻¹)/ε²` as `ε → 0`. The source's own bound
`n ≥ k(m² − m − 1) − 2m` (p.41) is vacuous at `m = 1`. -/
theorem theorem_4_3 :
    ∃ c ε₀ δ₀ : ℝ, 0 < c ∧ 0 < ε₀ ∧ 0 < δ₀ ∧
      ∀ m : ℕ, 2 ≤ m → ∀ ε δ : ℝ, 0 < ε → ε ≤ ε₀ → 0 < δ → δ ≤ δ₀ → ∀ n : ℕ,
        Learns (fermiPure m) purifiedDist n ε δ →
          c * (((m : ℝ) ^ 2 + Real.log δ⁻¹) / ε ^ 2) ≤ n := by sorry

end OptGaussTomo
