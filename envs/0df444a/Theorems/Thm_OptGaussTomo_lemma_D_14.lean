-- Prove2me | Theorems.Thm_OptGaussTomo_lemma_D_14
-- name    : OptGaussTomo.lemma_D_14
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T04:07:27.715204+00:00
-- url     : https://prove2.me/theorems/ae8e57ad-5c80-4d45-ba12-c9a0f85a43a1
-- title:
--   Lemma D.14 — covariance estimation in multiplicative error, $c_\varepsilon^{-1}V\preceq\hat V\preceq c_\varepsilon V$
-- statement:
--   Let $c_\varepsilon=\dfrac{1+\sqrt{\varepsilon^2(2-\varepsilon^2)}}{1-\sqrt{\varepsilon^2(2-\varepsilon^2)}}$. Then $c_\varepsilon=1+O(\varepsilon)$ as $\varepsilon\to0$, and there is a universal constant $C>0$ such that for every $m\ge1$ and $0<\varepsilon,\delta<1$ there are $M\le C(m^2+\log\delta^{-1})/\varepsilon^2$ and a measurement on $M$ copies with outcome a real matrix $\hat V$ such that, for every $m$-mode bosonic Gaussian state $\rho=\rho_{0,V}$ with zero first moment:
--
--   1. with probability at least $1-\delta$, $\;c_\varepsilon^{-1}V\preceq\hat V\preceq c_\varepsilon V$ (Loewner order);
--   2. with probability at least $1-\delta$, $\hat V$ is a valid covariance matrix and $\hat\rho=\rho_{0,\hat V}$ satisfies $F(\rho,\hat\rho)^2\ge1-\varepsilon^2$.
--
--   This multiplicative estimate is the seed for estimating the first moment in Theorem D.15.
--
--   Differences from the source:
--   - reading: a procedure for an unknown state ρ_{0,V} → one M-copy POVM fixed before ρ, working for every ρ; reason: read literally the procedure could depend on ρ (and output V); the proof and Theorem 5.1 use one procedure
--   - reading: O((m² + log(δ⁻¹))/ε²) copies → one universal constant C > 0, fixed before m, ε, δ, and some n ≤ C(m² + log δ⁻¹)/ε²; reason: meaning of O(·) uniform in m, ε, δ; log is natural; the range 0 < ε, δ < 1 is the one printed in Corollary C.6 and Theorem D.15
--   - reading: c_ε = 1 + O(ε) → constants K, ε₁ > 0 with c_ε ≤ 1 + Kε for 0 < ε ≤ ε₁; reason: meaning of O(ε) as ε → 0
--   - encoding: ρ̂ = ρ_{0,V̂} → V̂ is a valid covariance matrix and every Gaussian state with mean 0 and covariance V̂ satisfies the fidelity bound; reason: such a state exists exactly when V̂ is valid and is then unique
--   - encoding: m modes → m ≥ 1; reason: an m-mode system has at least one mode; the paper writes m ∈ ℕ+ (Lemma D.14)
-- source:
--   Chen, Fanizza, Girardi, Lami, Mele, Walter, Witteveen, Optimal tomography of bosonic and fermionic Gaussian states, arXiv:2607.11847 (held version, sha256 0f7548a2a5cfd55079e5d7f1787c97c8561a818a53d7e29824715104bad416ed), Lemma D.14 p.56 (pdf p.56)

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

/-- **Lemma D.14** (Covariance estimation in multiplicative error; Chen, Fanizza, Girardi, Lami,
Mele, Walter, Witteveen, *Optimal tomography of bosonic and fermionic Gaussian states*,
arXiv:2607.11847, held version, sha256 0f7548a2…, Lemma D.14, p.56). Let `0 < ε, δ < 1` and
`m ∈ ℕ⁺`. Let `ρ = ρ_{0,V}` be an unknown `m`-mode bosonic Gaussian state with zero first moment.
There is a procedure that, using `M = O((m² + log(δ⁻¹))/ε²)` copies of `ρ`, outputs a covariance
matrix `V̂` such that, with probability at least `1 − δ`, `c_ε⁻¹ V ⪯ V̂ ⪯ c_ε V`, where
`c_ε := (1 + √(ε²(2 − ε²)))/(1 − √(ε²(2 − ε²))) = 1 + O(ε)`. Moreover, if `ρ̂ = ρ_{0,V̂}`, then
`F(ρ, ρ̂)² ≥ 1 − ε²` with probability at least `1 − δ`.

**Formalization Note.** `O(·)` is one universal constant `C > 0` fixed before `m`, `ε`, `δ`.
The procedure is an `M`-copy POVM with outcomes `V̂` (real arrays on the interleaved quadratures)
fixed before the unknown state: the source's "unknown" state means the procedure does not depend
on `ρ` (read literally, a procedure depending on `ρ` could output `V` itself). `⪯` is the Loewner
order (`B − A` positive semidefinite). "`ρ̂ = ρ_{0,V̂}`" is the event that `V̂` is a valid covariance
matrix and every Gaussian state with mean `0` and covariance `V̂` (it is unique) has
`F(ρ, ρ̂)² ≥ 1 − ε²`. The two guarantees are stated as two events of probability `≥ 1 − δ`, as
printed. The clause `c_ε = 1 + O(ε)` (as `ε → 0`) is the first conjunct: `c_ε ≤ 1 + Kε` for
`0 < ε ≤ ε₁`, with constants `K, ε₁ > 0`. `F` is the root fidelity (`rootFidelity`); `log` is natural. -/
theorem lemma_D_14 :
    (∃ K ε₁ : ℝ, 0 < K ∧ 0 < ε₁ ∧ ∀ ε : ℝ, 0 < ε → ε ≤ ε₁ →
      (1 + Real.sqrt (ε ^ 2 * (2 - ε ^ 2))) / (1 - Real.sqrt (ε ^ 2 * (2 - ε ^ 2))) ≤ 1 + K * ε) ∧
    ∃ C : ℝ, 0 < C ∧ ∀ m : ℕ, 1 ≤ m → ∀ ε δ : ℝ, 0 < ε → ε < 1 → 0 < δ → δ < 1 →
      ∃ M : ℕ, (M : ℝ) ≤ C * (((m : ℝ) ^ 2 + Real.log δ⁻¹) / ε ^ 2) ∧
      ∃ E : BosonicLearn.FockPOVM (Fin M → Occupation (Fin m))
          (InterleavedQuadrature (Fin m) → InterleavedQuadrature (Fin m) → ℝ),
        ∀ (ρ : State (Occupation (Fin m))) (V : OscillatorCovariance (Fin m)),
          GaussianAt ρ.coefficients 0 V →
          ENNReal.ofReal (1 - δ) ≤ E.law (WildeQIT.Schumacher.tensorPow M ρ.coefficients)
            {Vh | (Matrix.of Vh - ((1 + Real.sqrt (ε ^ 2 * (2 - ε ^ 2))) /
                    (1 - Real.sqrt (ε ^ 2 * (2 - ε ^ 2))))⁻¹ • V).PosSemidef ∧
                  (((1 + Real.sqrt (ε ^ 2 * (2 - ε ^ 2))) /
                    (1 - Real.sqrt (ε ^ 2 * (2 - ε ^ 2)))) • V - Matrix.of Vh).PosSemidef} ∧
          ENNReal.ofReal (1 - δ) ≤ E.law (WildeQIT.Schumacher.tensorPow M ρ.coefficients)
            {Vh | IsValidCov (Matrix.of Vh) ∧
              ∀ ρh : State (Occupation (Fin m)), GaussianAt ρh.coefficients 0 (Matrix.of Vh) →
                1 - ε ^ 2 ≤ rootFidelity ρ.coefficients ρh.coefficients ^ 2} := by sorry

end OptGaussTomo
