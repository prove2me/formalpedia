-- Prove2me | Theorems.Thm_OptGaussTomo_corollary_C_6
-- name    : OptGaussTomo.corollary_C_6
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T04:09:09.946674+00:00
-- url     : https://prove2.me/theorems/2d278b2d-ca03-4048-8ebd-1ced4ef644b4
-- title:
--   Corollary C.6 — tomography of pure fermionic Gaussian states with $O((m^2+\log\delta^{-1})/\varepsilon^2)$ copies
-- statement:
--   There is a universal constant $C>0$ such that the following holds. Let $m\ge1$ and $0<\varepsilon,\delta<1$, and let $n\ge C\,(m^2+\log\delta^{-1})/\varepsilon^2$. For every pure fermionic Gaussian state $\psi\in\mathcal G_m$, the Gaussian Hayashi measurement $\mu_{n,m}$ applied to $\psi^{\otimes n}$ outputs an estimate $\hat\psi$ with
--
--   $$
--   |\langle\psi|\hat\psi\rangle|^2\ \ge\ 1-\varepsilon^2
--   $$
--
--   with probability at least $1-\delta$. This is the optimal pure-state protocol; Theorem 4.2 lifts it to mixed states.
--
--   Differences from the source:
--   - reading: given n = O((m² + log(δ⁻¹))/ε²) copies → one universal C > 0 and every n ≥ C(m² + log δ⁻¹)/ε²; reason: μ_{n,m} is a fixed family analysed for each n, and the paper's failure bound exp(−ε²⌊n/2⌋ + m(m−1)/2·log 2) decreases in n
--   - encoding: m modes → m ≥ 1; reason: an m-mode system has at least one mode; the paper writes m ∈ ℕ+ (Lemma D.14)
--   - encoding: the measurement μ_{n,m} outputs ψ̂ → the outcome law hayashiLaw n m of (C.7), outcome (s, U) standing for ψ̂ = Uψ_s; reason: this is the outcome distribution of μ_{n,m}
-- source:
--   Chen, Fanizza, Girardi, Lami, Mele, Walter, Witteveen, Optimal tomography of bosonic and fermionic Gaussian states, arXiv:2607.11847 (held version, sha256 0f7548a2a5cfd55079e5d7f1787c97c8561a818a53d7e29824715104bad416ed), Corollary C.6 pp.38–39 (pdf pp.38–39)

import Mathlib
import Definitions.Def_WildeQIT_Schumacher_tensorPow
import Definitions.Def_OptGaussTomo_gaussVecs
import Definitions.Def_OptGaussTomo_hayashiLaw

open FermiCap.Gaussian (Qubits Op)
open MeasureTheory

namespace OptGaussTomo

/-- **Corollary C.6** (Tomography of pure fermionic Gaussian states; Chen, Fanizza, Girardi, Lami,
Mele, Walter, Witteveen, *Optimal tomography of bosonic and fermionic Gaussian states*,
arXiv:2607.11847, held version, sha256 0f7548a2…, Corollary C.6, pp.38–39). Let `0 < ε, δ < 1`.
Given `n = O((m² + log(δ⁻¹))/ε²)` copies of a pure fermionic Gaussian state `ψ ∈ G_m`, the
measurement `μ_{n,m}` outputs an estimate `ψ̂` such that `|⟨ψ|ψ̂⟩|² ≥ 1 − ε²` with probability at
least `1 − δ`.

**Formalization Note.** "Given `n = O(·)` copies" is read with one universal constant `C`, fixed
before `m`, `ε`, `δ`: every `n ≥ C (m² + log δ⁻¹)/ε²` works (the measurement `μ_{n,m}` is a fixed
family, and the source's failure bound `exp(−ε²⌊n/2⌋ + m(m−1)/2 · log 2)` decreases in `n`).
`log` is the natural logarithm. The outcome `(s, U)` of `μ_{n,m}` stands for `ψ̂ = U ψ_s`
(`hayashiLaw`). `m ≥ 1` as for every `m`-mode system. -/
theorem corollary_C_6 :
    ∃ C : ℝ, 0 < C ∧ ∀ m : ℕ, 1 ≤ m → ∀ ε δ : ℝ, 0 < ε → ε < 1 → 0 < δ → δ < 1 →
      ∀ n : ℕ, C * (((m : ℝ) ^ 2 + Real.log δ⁻¹) / ε ^ 2) ≤ n →
      ∀ ψ : Qubits m → ℂ, (ψ ∈ gaussVecs m true ∨ ψ ∈ gaussVecs m false) →
        ENNReal.ofReal (1 - δ) ≤
          hayashiLaw n m (WildeQIT.Schumacher.tensorPow n (Matrix.vecMulVec ψ (star ψ)))
            {p | 1 - ε ^ 2 ≤ ‖star ψ ⬝ᵥ (p.2 : Op m).mulVec (gaussRef m p.1)‖ ^ 2} := by sorry

end OptGaussTomo
