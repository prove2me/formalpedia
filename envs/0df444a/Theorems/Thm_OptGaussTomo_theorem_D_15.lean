-- Prove2me | Theorems.Thm_OptGaussTomo_theorem_D_15
-- name    : OptGaussTomo.theorem_D_15
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T04:07:40.573473+00:00
-- url     : https://prove2.me/theorems/aa2f565d-601a-4091-b61b-a71b0e4898a0
-- title:
--   Theorem D.15 — tomography of mixed bosonic Gaussian states with non-zero first moments
-- statement:
--   There are universal constants $C,K>0$ such that for every $m\ge1$ and $0<\varepsilon,\delta<1$ there are $n\le C(m^2+\log\delta^{-1})/\varepsilon^2$ and a measurement on $n$ copies with outcome $(\hat\mu,\hat V)$ such that for every $m$-mode bosonic Gaussian state $\rho=\rho_{\mu,V}$, with probability at least $1-\delta$, all of the following hold on one event:
--
--   1. $\hat V$ is a valid covariance matrix and the Gaussian state $\hat\rho=\rho_{\hat\mu,\hat V}$ satisfies $F(\rho,\hat\rho)^2\ge1-\varepsilon^2$;
--   2. $(1-K\varepsilon)V\preceq\hat V\preceq(1+K\varepsilon)V$;
--   3. $$(\hat\mu-\mu)^{\mathsf T}V^{-1}(\hat\mu-\mu)\ \le\ K\,\varepsilon^2\,\frac{m+\log(\delta^{-1})}{m^2+\log(\delta^{-1})}.$$
--
--   This is the bosonic upper bound for general (mixed, displaced) Gaussian states, with no energy bound.
--
--   Differences from the source:
--   - reading: Let ρ = ρ_{μ,V} be arbitrary … there is a tomography protocol → one n-copy POVM fixed before ρ, working for every ρ; reason: read literally the protocol could depend on ρ, which is trivial; the proof and Theorem 5.1 use one protocol for the unknown state
--   - reading: O((m² + log(δ⁻¹))/ε²) copies → one universal constant C > 0, fixed before m, ε, δ, and some n ≤ C(m² + log δ⁻¹)/ε²; reason: meaning of O(·) uniform in m, ε, δ; log is natural; the range 0 < ε, δ < 1 is the one printed in Corollary C.6 and Theorem D.15
--   - reading: f_ε = O(ε) and (μ̂ − μ)ᵀV⁻¹(μ̂ − μ) = O(ε²(m + log δ⁻¹)/(m² + log δ⁻¹)) → one universal K > 0 with f_ε replaced by Kε and the quadratic form ≤ Kε²(m + log δ⁻¹)/(m² + log δ⁻¹), for all 0 < ε, δ < 1; reason: meaning of O(·) uniform in m, ε, δ; the proof's last paragraph shows the constants can be taken uniform on (0,1)
--   - encoding: outputs a Gaussian state ρ̂ = ρ_{μ̂,V̂} → the outcome is (μ̂, V̂); on the event V̂ is valid and every Gaussian state with mean μ̂ and covariance V̂ satisfies the fidelity bound; reason: such a state exists exactly when V̂ is valid and is then unique
--   - encoding: m modes → m ≥ 1; reason: an m-mode system has at least one mode; the paper writes m ∈ ℕ+ (Lemma D.14)
-- source:
--   Chen, Fanizza, Girardi, Lami, Mele, Walter, Witteveen, Optimal tomography of bosonic and fermionic Gaussian states, arXiv:2607.11847 (held version, sha256 0f7548a2a5cfd55079e5d7f1787c97c8561a818a53d7e29824715104bad416ed), Theorem D.15 p.58 (pdf p.58)

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P33
import Definitions.Def_QAlgorithms_Papers_Independent_Support50_P14
import Definitions.Def_WildeQIT_Schumacher_tensorPow
import Definitions.Def_BosonicLearn_FockPOVM
import Definitions.Def_OptGaussTomo_rootFidelity
import Definitions.Def_OptGaussTomo_IsValidCov

open QAlgorithms.Papers.Independent.Dependency50.P33 (State)
open QAlgorithms.Papers.Independent.Claimed50.P47 (Occupation)
open QAlgorithms.Papers.Independent.Support50.P14 (InterleavedQuadrature OscillatorCovariance GaussianAt)

namespace OptGaussTomo

/-- **Theorem D.15** (Tomography of mixed bosonic Gaussian states with non-zero first moments;
Chen, Fanizza, Girardi, Lami, Mele, Walter, Witteveen, *Optimal tomography of bosonic and fermionic
Gaussian states*, arXiv:2607.11847, held version, sha256 0f7548a2…, Theorem D.15, p.58). Let
`ρ = ρ_{μ,V}` be an arbitrary `m`-mode bosonic Gaussian state. For every `0 < ε, δ < 1`, there is a
tomography protocol which uses `O((m² + log(δ⁻¹))/ε²)` copies of `ρ` and outputs a Gaussian state
`ρ̂ = ρ_{μ̂,V̂}` such that, with probability at least `1 − δ`, `F(ρ, ρ̂)² ≥ 1 − ε²`. Moreover, on the
same event, `μ̂` and `V̂` satisfy `(1 − f_ε)V ⪯ V̂ ⪯ (1 + f_ε)V`, where `f_ε = O(ε)`, and
`(μ̂ − μ)ᵀV⁻¹(μ̂ − μ) = O(ε² (m + log(δ⁻¹))/(m² + log(δ⁻¹)))`.

**Formalization Note.** The `O(·)`s are universal constants `C, K > 0` fixed before `m ≥ 1` and
`0 < ε, δ < 1`; `f_ε = O(ε)` is read as `f_ε ≤ Kε`, i.e. `f_ε` is replaced by `Kε`. The protocol
is an `n`-copy POVM with outcomes `(μ̂, V̂)` fixed **before** `ρ` (read literally, "Let `ρ` be …
there is a protocol" would allow a protocol depending on `ρ`, which is trivial; the proof and
Theorem 5.1 use one protocol for the unknown state). "Outputs a Gaussian state `ρ_{μ̂,V̂}`" is the
clause that `V̂` is a valid covariance matrix; the fidelity clause is for every (the unique) state
with mean `μ̂` and covariance `V̂`. All clauses hold on one event of probability `≥ 1 − δ`.
`⪯` is the Loewner order, `V⁻¹` the matrix inverse (a valid covariance matrix is positive definite),
`F` the root fidelity, `log` natural. -/
theorem theorem_D_15 :
    ∃ C K : ℝ, 0 < C ∧ 0 < K ∧ ∀ m : ℕ, 1 ≤ m → ∀ ε δ : ℝ, 0 < ε → ε < 1 → 0 < δ → δ < 1 →
      ∃ n : ℕ, (n : ℝ) ≤ C * (((m : ℝ) ^ 2 + Real.log δ⁻¹) / ε ^ 2) ∧
      ∃ E : BosonicLearn.FockPOVM (Fin n → Occupation (Fin m))
          ((InterleavedQuadrature (Fin m) → ℝ) ×
            (InterleavedQuadrature (Fin m) → InterleavedQuadrature (Fin m) → ℝ)),
        ∀ (ρ : State (Occupation (Fin m))) (μ : InterleavedQuadrature (Fin m) → ℝ)
          (V : OscillatorCovariance (Fin m)), GaussianAt ρ.coefficients μ V →
          ENNReal.ofReal (1 - δ) ≤ E.law (WildeQIT.Schumacher.tensorPow n ρ.coefficients)
            {p | IsValidCov (Matrix.of p.2) ∧
              (∀ ρh : State (Occupation (Fin m)), GaussianAt ρh.coefficients p.1 (Matrix.of p.2) →
                1 - ε ^ 2 ≤ rootFidelity ρ.coefficients ρh.coefficients ^ 2) ∧
              (Matrix.of p.2 - (1 - K * ε) • V).PosSemidef ∧
              ((1 + K * ε) • V - Matrix.of p.2).PosSemidef ∧
              (p.1 - μ) ⬝ᵥ (V⁻¹).mulVec (p.1 - μ) ≤
                K * (ε ^ 2 * (((m : ℝ) + Real.log δ⁻¹) / ((m : ℝ) ^ 2 + Real.log δ⁻¹)))} := by sorry

end OptGaussTomo
