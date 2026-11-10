-- Prove2me | Theorems.Thm_OptGaussTomo_eq_A_5
-- name    : OptGaussTomo.eq_A_5
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T04:06:07.286808+00:00
-- url     : https://prove2.me/theorems/2e71c06d-758e-4fee-8408-d27d6eb7bd9e
-- title:
--   Eq. (A.5) — optimal error for distinguishing $\psi^{\otimes n}$ from $\phi^{\otimes n}$ (corrected: $\Omega(e^{-\varepsilon^2 n})$ as $e^{-2\varepsilon^2n}/4$)
-- statement:
--   Let $\psi,\phi$ be unit vectors in $\mathbb C^d$ with $|\langle\psi|\phi\rangle|^2=1-\varepsilon^2$, and consider deciding, with equal prior probabilities, whether $n$ given copies are $\psi^{\otimes n}$ or $\phi^{\otimes n}$. The optimal failure probability $\delta^\star$, the infimum over effects $0\le E\le I$ of $\tfrac12\langle\psi^{\otimes n}|(I-E)|\psi^{\otimes n}\rangle+\tfrac12\langle\phi^{\otimes n}|E|\phi^{\otimes n}\rangle$, satisfies
--
--   $$
--   \delta^\star=\tfrac12\big(1-T(\psi^{\otimes n},\phi^{\otimes n})\big)=\tfrac12\Big(1-\sqrt{1-(1-\varepsilon^2)^n}\Big)\ \ge\ \frac{(1-\varepsilon^2)^n}{4},
--   $$
--
--   and $(1-\varepsilon^2)^n/4\ge e^{-2\varepsilon^2n}/4$ whenever $\varepsilon^2\le\tfrac12$. This reduction gives the $\log(\delta^{-1})/\varepsilon^2$ term of the lower bounds.
--
--   Differences from the source:
--   - correction: δ ≥ (1 − ε²)^n/4 = Ω(exp(−ε²n)) → (1 − ε²)^n/4 ≥ exp(−2ε²n)/4 for ε² ≤ ½; reason: read literally (a constant factor times exp(−ε²n)) the tail is false: at ε² = ½, (1 − ε²)^n/4 = 2^{−n}/4 while exp(−ε²n) = e^{−n/2}, and 2^{−n}/e^{−n/2} → 0; the intended meaning exp(−O(ε²n)) is stated with an explicit constant
--   - encoding: the optimal probability of failure for this task → the infimum over effects 0 ≤ E ≤ I of the equal-prior average error; reason: the Helstrom setting of the paper's reduction
--   - encoding: states on ℂ^d → unit vectors on ℂ^I for a finite index type I; reason: same setting (§A.1)
--   - encoding: T(ψ^{⊗n}, ϕ^{⊗n}) → (BosonicLearn.traceDist Ψ Φ).toReal for the projectors Ψ, Φ; reason: the published trace distance is valued in [0, ∞] and is finite on these projectors
-- source:
--   Chen, Fanizza, Girardi, Lami, Mele, Walter, Witteveen, Optimal tomography of bosonic and fermionic Gaussian states, arXiv:2607.11847 (held version, sha256 0f7548a2a5cfd55079e5d7f1787c97c8561a818a53d7e29824715104bad416ed), §A.1 p.24 (pdf p.24), eq. (A.5)

import Mathlib
import Definitions.Def_WildeQIT_Schumacher_tensorPow
import Definitions.Def_BosonicLearn_traceDist

open scoped ComplexOrder

namespace OptGaussTomo

/-- **Eq. (A.5)** (Chen, Fanizza, Girardi, Lami, Mele, Walter, Witteveen, *Optimal tomography of
bosonic and fermionic Gaussian states*, arXiv:2607.11847, held version, sha256 0f7548a2…, §A.1, p.24,
eq. (A.5)). For two pure states `|ψ⟩, |ϕ⟩` with `|⟨ψ|ϕ⟩|² = 1 − ε²`, given access to either
`|ψ⟩^{⊗n}` or `|ϕ⟩^{⊗n}`, "the optimal probability of failure for this task is given by the trace
distance: it equals `δ = ½(1 − T(ψ^{⊗n}, ϕ^{⊗n})) = ½(1 − √(1 − (1 − ε²)^n)) ≥ (1 − ε²)^n/4`".

**Formalization Note.** The states live on `ℂ^I` with `I` finite (the setting of §A.1 is `ℂ^d`).
The task is to decide between `ψ^{⊗n}` and `ϕ^{⊗n}` with equal priors; a test is an effect
`0 ≤ E ≤ I` on the `n`-copy space (outcome "`ϕ`"), its failure probability is
`½⟨ψ^{⊗n}|(I − E)|ψ^{⊗n}⟩ + ½⟨ϕ^{⊗n}|E|ϕ^{⊗n}⟩`, and the optimal failure probability is the
infimum over all tests. `T` is the published `BosonicLearn.traceDist` (`½‖·‖₁`, finite on these projectors, converted
to a real number) of `tensorPow n (|ψ⟩⟨ψ|)` and `tensorPow n (|ϕ⟩⟨ϕ|)` (published
`WildeQIT.Schumacher.tensorPow`). `n` is any number of copies.

**Correction.** The tail "`= Ω(exp(−ε²n))`" is false read literally (a constant factor in front of
`exp(−ε²n)`): at `ε² = ½`, `(1 − ε²)^n/4 = 2^{−n}/4` while `exp(−ε²n) = e^{−n/2}`, and
`2^{−n}/e^{−n/2} → 0`. It is stated in its intended sense `exp(−O(ε²n))`, with the explicit
constant: `(1 − ε²)^n/4 ≥ exp(−2ε²n)/4` for `ε² ≤ ½`. -/
theorem eq_A_5 {I : Type} [Fintype I] [DecidableEq I] (ψ ϕ : I → ℂ)
    (hψ : star ψ ⬝ᵥ ψ = 1) (hϕ : star ϕ ⬝ᵥ ϕ = 1) (ε : ℝ)
    (hε : ‖star ψ ⬝ᵥ ϕ‖ ^ 2 = 1 - ε ^ 2) (n : ℕ) :
    sInf {p : ℝ | ∃ E : Matrix (Fin n → I) (Fin n → I) ℂ, E.PosSemidef ∧ (1 - E).PosSemidef ∧
        p = ((1 - E) * WildeQIT.Schumacher.tensorPow n (Matrix.vecMulVec ψ (star ψ))).trace.re / 2 +
          (E * WildeQIT.Schumacher.tensorPow n (Matrix.vecMulVec ϕ (star ϕ))).trace.re / 2} =
      (1 - (BosonicLearn.traceDist (WildeQIT.Schumacher.tensorPow n (Matrix.vecMulVec ψ (star ψ)))
        (WildeQIT.Schumacher.tensorPow n (Matrix.vecMulVec ϕ (star ϕ)))).toReal) / 2 ∧
    (1 - (BosonicLearn.traceDist (WildeQIT.Schumacher.tensorPow n (Matrix.vecMulVec ψ (star ψ)))
        (WildeQIT.Schumacher.tensorPow n (Matrix.vecMulVec ϕ (star ϕ)))).toReal) / 2 =
      (1 - Real.sqrt (1 - (1 - ε ^ 2) ^ n)) / 2 ∧
    (1 - ε ^ 2) ^ n / 4 ≤ (1 - Real.sqrt (1 - (1 - ε ^ 2) ^ n)) / 2 ∧
    (ε ^ 2 ≤ 1 / 2 → Real.exp (-(2 * ε ^ 2 * n)) / 4 ≤ (1 - ε ^ 2) ^ n / 4) := by sorry

end OptGaussTomo
