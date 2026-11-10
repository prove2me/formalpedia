-- Prove2me | Theorems.Thm_OptGaussTomo_lemma_C_7
-- name    : OptGaussTomo.lemma_C_7
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T04:07:47.732593+00:00
-- url     : https://prove2.me/theorems/7c4cd89f-7923-4d6e-bcc5-d5da4f5025ca
-- title:
--   Lemma C.7 — average fidelity bound $\mathbf E_\psi\mathbf E_{\hat\psi}|\langle\psi|\hat\psi\rangle|^{2k}\le d_{n,m}/d_{n+k,m}$
-- statement:
--   Let $m\ge1$, $n,k\in\mathbb N$ and $s\in\{+,-\}$. Let $\mu$ be any measurement on $n$ copies whose estimates $\hat\psi$ lie in $\mathcal G^s_m$, and let $P_\psi$ be its outcome law on $|\psi\rangle\langle\psi|^{\otimes n}$. If $\psi$ is distributed according to the Haar (Gaussian-unitarily invariant) probability measure on $\mathcal G^s_m$, then
--
--   $$
--   \mathbf E_\psi\,\mathbf E_{\hat\psi\sim P_\psi}\,|\langle\psi|\hat\psi\rangle|^{2k}\ \le\ \frac{d_{n,m}}{d_{n+k,m}} .
--   $$
--
--   Averaging over random Gaussian states in this way gives the lower bound of Theorem 4.3.
--
--   Differences from the source:
--   - encoding: m modes → m ≥ 1; reason: an m-mode system has at least one mode; the paper writes m ∈ ℕ+ (Lemma D.14)
--   - encoding: the Haar measure on G^±_m → ψ = Uψ_s with U distributed by the Haar probability measure on Gaussian unitaries; reason: the invariant probability measure on G^s_m is this push-forward
--   - encoding: the estimate from the measurement μ → any POVM with outcomes in vectors whose outcome law on every density is concentrated on G^s_m; reason: the paper's estimate lies in G^s_m (p.40)
-- source:
--   Chen, Fanizza, Girardi, Lami, Mele, Walter, Witteveen, Optimal tomography of bosonic and fermionic Gaussian states, arXiv:2607.11847 (held version, sha256 0f7548a2a5cfd55079e5d7f1787c97c8561a818a53d7e29824715104bad416ed), Lemma C.7 p.40 (pdf p.40)

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P33
import Definitions.Def_WildeQIT_Schumacher_tensorPow
import Definitions.Def_BosonicLearn_FockPOVM
import Definitions.Def_OptGaussTomo_gaussVecs
import Definitions.Def_OptGaussTomo_dFermi
import Definitions.Def_OptGaussTomo_fermiHaar

open QAlgorithms.Papers.Independent.Dependency50.P33 (IsDensity)
open FermiCap.Gaussian (Qubits Op)
open MeasureTheory
open scoped ENNReal

namespace OptGaussTomo

/-- **Lemma C.7** (Chen, Fanizza, Girardi, Lami, Mele, Walter, Witteveen, *Optimal tomography of
bosonic and fermionic Gaussian states*, arXiv:2607.11847, held version, sha256 0f7548a2…, Lemma C.7,
p.40). Suppose that `ψ` is distributed according to the Haar measure on `G⁺_m` or on `G⁻_m`, and
`ψ̂` denotes the estimate from the measurement `μ` on `n` copies of `ψ`. Then
`E_ψ E_{ψ̂∼P_ψ} |⟨ψ|ψ̂⟩|^{2k} ≤ d_{n,m}/d_{n+k,m}`, with `d_{n,m}` as in (C.6).

**Formalization Note.** `μ` is any POVM on `n` copies whose estimates lie in `G^s_m`
(`gaussVecs m s`, the parity sector of `ψ`; p.40: "an estimate `|ψ̂⟩ ∈ H⁺_m` … itself an
even-parity pure Gaussian fermionic state"): its outcome law on every density is concentrated on
`G^s_m`. `P_ψ` is the outcome law of `μ` on `|ψ⟩⟨ψ|^{⊗n}` (`tensorPow n`). The Haar measure on
`G^s_m` is the push-forward of `fermiHaar m` under `U ↦ U ψ_s` (`gaussRef m s`), so `ψ = U ψ_s`
with `U` Haar distributed. The expectations are `ℝ≥0∞`-valued integrals of a nonnegative
integrand (no integrability side condition). `k` is any natural number, `m ≥ 1`. -/
theorem lemma_C_7 (m n k : ℕ) (hm : 1 ≤ m) (s : Bool)
    (μ : BosonicLearn.FockPOVM (Fin n → Qubits m) (Qubits m → ℂ))
    (hμ : ∀ ρ, IsDensity ρ → μ.law ρ (gaussVecs m s)ᶜ = 0) :
    ∫⁻ U : fermiGaussGroup m,
        ∫⁻ ϕ, (‖star ((U : Op m).mulVec (gaussRef m s)) ⬝ᵥ ϕ‖₊ : ℝ≥0∞) ^ (2 * k)
          ∂(μ.law (WildeQIT.Schumacher.tensorPow n (Matrix.vecMulVec ((U : Op m).mulVec (gaussRef m s))
              (star ((U : Op m).mulVec (gaussRef m s))))))
        ∂(fermiHaar m) ≤
      ENNReal.ofReal (dFermi n m / dFermi (n + k) m) := by sorry

end OptGaussTomo
