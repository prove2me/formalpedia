-- Prove2me | Theorems.Thm_OptGaussTomo_main_result
-- name    : OptGaussTomo.main_result
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T04:07:57.661053+00:00
-- url     : https://prove2.me/theorems/6bcb66cb-2a39-4af1-a770-345311cae143
-- title:
--   Theorem (Main result) — learning $m$-mode Gaussian states takes $\Theta((m^2+\log\delta^{-1})/\varepsilon^2)$ copies (corrected: pure fermionic lower bound for $m\ge2$)
-- statement:
--   There are universal constants $C,c,\varepsilon_0,\delta_0>0$ such that the following holds for each of the four classes — $m$-mode fermionic Gaussian states, pure fermionic Gaussian states, bosonic Gaussian states (any mean, no energy bound), pure bosonic Gaussian states — and each of the two accuracy measures, purified distance $P$ and trace distance $T$.
--
--   1. **Upper bound.** For every $m\ge1$ and $0<\varepsilon,\delta<1$ there is a measurement on $n\le C\,(m^2+\log\delta^{-1})/\varepsilon^2$ copies that, for every state $\rho$ of the class, outputs an estimate $\hat\rho$ with $\mathrm{dist}(\rho,\hat\rho)\le\varepsilon$ with probability at least $1-\delta$.
--   2. **Lower bound.** For every $m\ge1$ (for pure fermionic states, every $m\ge2$), $0<\varepsilon\le\varepsilon_0$ and $0<\delta\le\delta_0$, every $n$ for which such a measurement exists satisfies
--
--   $$
--   n\ \ge\ c\,\frac{m^2+\log(\delta^{-1})}{\varepsilon^2}.
--   $$
--
--   Thus the sample complexity of learning an $m$-mode Gaussian state is $n=\Theta\big((m^2+\log(\delta^{-1}))/\varepsilon^2\big)$, the same form as for arbitrary $d$-dimensional states with the dimension $d$ replaced by the number of modes $m$.
--
--   The paper proves the lower bounds for pure states; the mixed-fermionic lower bound at $m=1$ is not covered by that argument (it follows from estimating the diagonal state $\mathrm{diag}(p,1-p)$, a classical coin).
--
--   Differences from the source:
--   - correction: the lower bound for pure fermionic Gaussian states, every m → m ≥ 2 for the pure-fermionic lower-bound clauses (all other clauses m ≥ 1); reason: at m = 1 the pure fermionic Gaussian states are |0⟩ and |1⟩ only (every quadratic Hamiltonian (C.2) is a multiple of Z), so one Z measurement on one copy learns them exactly and n = 1 succeeds for every ε, δ
--   - reading: n = Θ((m² + log(δ⁻¹))/ε²) → universal C, c, ε₀, δ₀ > 0 fixed before m, ε, δ: for 0 < ε, δ < 1 some n ≤ C(m² + log δ⁻¹)/ε² succeeds; for 0 < ε ≤ ε₀, 0 < δ ≤ δ₀ every successful n is ≥ c(m² + log δ⁻¹)/ε²; one set of constants for all eight clauses; reason: meaning of Θ; the lower bound can hold only for small ε, δ; with finitely many clauses one set of constants is equivalent to separate ones
--   - reading: outputs an estimate ψ̂ → the estimate is an arbitrary density operator; reason: the stronger lower bound; the paper takes a pure Gaussian estimate without loss of generality (p.40)
--   - encoding: a tomography protocol using n copies → an n-copy POVM with density-operator outcomes, fixed before the unknown state (Learns); reason: any measurement with classical post-processing is such a POVM; the protocol may not depend on the state
--   - encoding: m modes → m ≥ 1; reason: an m-mode system has at least one mode; the paper writes m ∈ ℕ+ (Lemma D.14)
--   - encoding: Gaussian states (Gibbs states of quadratic Hamiltonians and limits) → FermiCap.Gaussian.IsEvenGaussian for fermions and Support50.P14.GaussianAt (any mean, covariance with vacuum I, no energy bound) for bosons; pure = idempotent / rank one; reason: standard equivalent characterizations of the same classes
--   - encoding: fidelity F(ρ, ρ̂) → root fidelity in Uhlmann form (supremum of |⟨u, v⟩| over purifications); reason: equals ‖√ρ√ρ̂‖₁ by Uhlmann's theorem
--   - encoding: trace distance T(ρ, ρ̂) = ½‖ρ − ρ̂‖₁ → the real number (BosonicLearn.traceDist ρ ρ̂).toReal; reason: the published trace distance is valued in [0, ∞] and is at most 1 on states, so the conversion is faithful
--   - encoding: n copies ρ^{⊗n} → the coefficient array on the basis Fin n → I with entries ∏ₜ ρ(x t, y t); reason: the n-fold tensor power; fermionic Gaussian states are even, so the qubit and fermionic tensor products agree
-- source:
--   Chen, Fanizza, Girardi, Lami, Mele, Walter, Witteveen, Optimal tomography of bosonic and fermionic Gaussian states, arXiv:2607.11847 (held version, sha256 0f7548a2a5cfd55079e5d7f1787c97c8561a818a53d7e29824715104bad416ed), Theorem (Main result), eq. (1.2), p.3 (pdf p.3)

import Mathlib
import Definitions.Def_OptGaussTomo_Learns
import Definitions.Def_BosonicLearn_traceDist
import Definitions.Def_OptGaussTomo_purifiedDist
import Definitions.Def_OptGaussTomo_fermiGauss
import Definitions.Def_OptGaussTomo_boseGauss

namespace OptGaussTomo

/-- **Theorem (Main result)** (Chen, Fanizza, Girardi, Lami, Mele, Walter, Witteveen, *Optimal
tomography of bosonic and fermionic Gaussian states*, arXiv:2607.11847, held version,
sha256 0f7548a2…, Theorem (Main result), eq. (1.2), p.3). The sample complexity of learning a bosonic
or fermionic Gaussian state on `m` modes to accuracy `ε` in purified distance or trace distance with
probability of error at most `δ` is `n = Θ((m² + log(δ⁻¹))/ε²)`. This holds regardless of whether
the state is promised to be pure or not.

**Formalization Note.**
* `Θ` is read with universal constants `C, c, ε₀, δ₀ > 0`, fixed before `m`, `ε`, `δ`:
  **upper bound** — for every `m ≥ 1` and `0 < ε, δ < 1` some `n ≤ C(m² + log δ⁻¹)/ε²` admits a
  successful `n`-copy protocol; **lower bound** — for `0 < ε ≤ ε₀`, `0 < δ ≤ δ₀`, every `n` that admits
  a successful protocol satisfies `n ≥ c(m² + log δ⁻¹)/ε²`. (A lower bound with a `log δ⁻¹` term can
  hold only for small `ε`, `δ`; for `δ ≥ 1` a protocol without copies succeeds.) One set of constants
  serves all eight (system, class, distance) combinations, each written out. `log` is natural.
* A protocol is an `n`-copy POVM with state-valued outcomes, fixed before the unknown state, and
  success means: for every state of the class, the estimate is within `ε` with probability
  `≥ 1 − δ` (`Learns`). Estimates are arbitrary states (also when the class is pure).
* Classes: `fermiGauss m`, `fermiPure m` (published `FermiCap.Gaussian.IsEvenGaussian`, `IsPure`),
  `boseGauss m`, `bosePure m` (published `Support50.P14.GaussianAt`: any mean, any covariance,
  no energy bound). Distances: `purifiedDist` (`√(1 − F²)`, root fidelity in Uhlmann form) and
  the published `BosonicLearn.traceDist` (`½‖·‖₁`, valued in `ℝ≥0∞`, finite on states; converted
  to a real number).
* **Correction:** the lower bound for pure fermionic Gaussian states is stated for `m ≥ 2`. At
  `m = 1` the pure fermionic Gaussian states are `|0⟩` and `|1⟩` only (every quadratic Hamiltonian
  (C.2) is a multiple of `Z`), so one `Z` measurement on one copy learns them exactly and `n = 1`
  succeeds for every `ε, δ`. All other clauses are for every `m ≥ 1`. -/
theorem main_result :
    ∃ C c ε₀ δ₀ : ℝ, 0 < C ∧ 0 < c ∧ 0 < ε₀ ∧ 0 < δ₀ ∧
      (∀ m : ℕ, 1 ≤ m → ∀ ε δ : ℝ, 0 < ε → ε < 1 → 0 < δ → δ < 1 →
        (∃ n : ℕ, (n : ℝ) ≤ C * (((m : ℝ) ^ 2 + Real.log δ⁻¹) / ε ^ 2) ∧
          Learns (fermiGauss m) purifiedDist n ε δ) ∧
        (∃ n : ℕ, (n : ℝ) ≤ C * (((m : ℝ) ^ 2 + Real.log δ⁻¹) / ε ^ 2) ∧
          Learns (fermiGauss m) (fun ρ σ => (BosonicLearn.traceDist ρ σ).toReal) n ε δ) ∧
        (∃ n : ℕ, (n : ℝ) ≤ C * (((m : ℝ) ^ 2 + Real.log δ⁻¹) / ε ^ 2) ∧
          Learns (fermiPure m) purifiedDist n ε δ) ∧
        (∃ n : ℕ, (n : ℝ) ≤ C * (((m : ℝ) ^ 2 + Real.log δ⁻¹) / ε ^ 2) ∧
          Learns (fermiPure m) (fun ρ σ => (BosonicLearn.traceDist ρ σ).toReal) n ε δ) ∧
        (∃ n : ℕ, (n : ℝ) ≤ C * (((m : ℝ) ^ 2 + Real.log δ⁻¹) / ε ^ 2) ∧
          Learns (boseGauss m) purifiedDist n ε δ) ∧
        (∃ n : ℕ, (n : ℝ) ≤ C * (((m : ℝ) ^ 2 + Real.log δ⁻¹) / ε ^ 2) ∧
          Learns (boseGauss m) (fun ρ σ => (BosonicLearn.traceDist ρ σ).toReal) n ε δ) ∧
        (∃ n : ℕ, (n : ℝ) ≤ C * (((m : ℝ) ^ 2 + Real.log δ⁻¹) / ε ^ 2) ∧
          Learns (bosePure m) purifiedDist n ε δ) ∧
        (∃ n : ℕ, (n : ℝ) ≤ C * (((m : ℝ) ^ 2 + Real.log δ⁻¹) / ε ^ 2) ∧
          Learns (bosePure m) (fun ρ σ => (BosonicLearn.traceDist ρ σ).toReal) n ε δ)) ∧
      (∀ m : ℕ, 1 ≤ m → ∀ ε δ : ℝ, 0 < ε → ε ≤ ε₀ → 0 < δ → δ ≤ δ₀ → ∀ n : ℕ,
        (Learns (fermiGauss m) purifiedDist n ε δ →
          c * (((m : ℝ) ^ 2 + Real.log δ⁻¹) / ε ^ 2) ≤ n) ∧
        (Learns (fermiGauss m) (fun ρ σ => (BosonicLearn.traceDist ρ σ).toReal) n ε δ →
          c * (((m : ℝ) ^ 2 + Real.log δ⁻¹) / ε ^ 2) ≤ n) ∧
        (2 ≤ m → Learns (fermiPure m) purifiedDist n ε δ →
          c * (((m : ℝ) ^ 2 + Real.log δ⁻¹) / ε ^ 2) ≤ n) ∧
        (2 ≤ m → Learns (fermiPure m) (fun ρ σ => (BosonicLearn.traceDist ρ σ).toReal) n ε δ →
          c * (((m : ℝ) ^ 2 + Real.log δ⁻¹) / ε ^ 2) ≤ n) ∧
        (Learns (boseGauss m) purifiedDist n ε δ →
          c * (((m : ℝ) ^ 2 + Real.log δ⁻¹) / ε ^ 2) ≤ n) ∧
        (Learns (boseGauss m) (fun ρ σ => (BosonicLearn.traceDist ρ σ).toReal) n ε δ →
          c * (((m : ℝ) ^ 2 + Real.log δ⁻¹) / ε ^ 2) ≤ n) ∧
        (Learns (bosePure m) purifiedDist n ε δ →
          c * (((m : ℝ) ^ 2 + Real.log δ⁻¹) / ε ^ 2) ≤ n) ∧
        (Learns (bosePure m) (fun ρ σ => (BosonicLearn.traceDist ρ σ).toReal) n ε δ →
          c * (((m : ℝ) ^ 2 + Real.log δ⁻¹) / ε ^ 2) ≤ n)) := by sorry

end OptGaussTomo
