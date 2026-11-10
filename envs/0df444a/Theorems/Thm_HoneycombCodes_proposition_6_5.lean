-- Prove2me | Theorems.Thm_HoneycombCodes_proposition_6_5
-- name    : HoneycombCodes.proposition_6_5
-- status  : Open
-- author  : @iris
-- created : 2026-11-09T22:31:08.458171+00:00
-- url     : https://prove2.me/theorems/3d5817f3-b10d-4a8d-ae31-99299a206597
-- title:
--   Proposition 6.5 — the symmetric slice is the fully optimized second MRRW bound
-- statement:
--   Fix $0<\delta<1/2$, put $s=1-2\delta$, restrict the balanced family to $x=1/2$, and write $\tau=\sin t$. For $0\le\tau\le s$ its spectral boundary is
--
--   $$
--   P=\frac{s-\tau}{1-\tau},\qquad E^2=(1+\tau)(s-\tau), \tag{67}
--   $$
--
--   and its objective is $\Phi_{bal}(\tfrac12,t;\delta)=F_\delta(\tau)$ (68). Consequently the infimum of the symmetric honeycomb slice ($x=1/2$, $\eta=\rho$) is exactly $M_2(\delta)$, and
--
--   $$
--   \kappa_{HC}(\delta)\le\kappa_{bal}(\delta)\le M_2(\delta).
--   $$
--
--   This gives the containment $\kappa_{HC}\le M_2$ of part (ii) of the main theorem.
--
--   **Formalization Note** (67)–(68) are identities for $P_{bal}$, $E_{bal}$, $\Phi_{bal}$ at $x=1/2$ and $0\le t\le\arcsin s$. The symmetric slice is the part of the feasible set of (9) with $x=1/2$ and $\eta=\rho$.
--
--   Differences from the source:
--
--   - encoding: 0 ≤ τ = sin t ≤ s → 0 ≤ t ≤ arcsin s; reason: sin is a bijection from [0, arcsin s] onto [0, s]
--   - reading: 'the infimum of the symmetric honeycomb slice' → sInf of Φ_HC over {q ∈ D_HC : x = 1/2, η = ρ, Γ_HC(q) > 1 − 2δ}; reason: the slice x = 1/2, η = ρ of the feasible set of (9), as in the proof's second paragraph (p.32)
-- source:
--   W. Gay, F. Granha Jeronimo, L. Liu, The Honeycomb Framework for Code Bounds, arXiv:2608.20287v2 (sha256 f4b07e318538a352116042dc4da0d4e9d47cfd979cf302c7fce3324584a3cd51), §6.3, Proposition 6.5, eqs. (67)–(68), p.31 (PDF 33)

import Mathlib
import Definitions.Def_HoneycombCodes_kappaHC
import Definitions.Def_HoneycombCodes_kappaBal
import Definitions.Def_HoneycombCodes_M2

set_option autoImplicit false

namespace HoneycombCodes

/-- **Proposition 6.5**, Gay, Granha Jeronimo, Liu, *The Honeycomb Framework for Code Bounds*, arXiv:2608.20287v2 (sha256 f4b07e31…cd51), p.31 (PDF 33). Fix `0 < δ < 1/2`, `s = 1 − 2δ`, restrict the
balanced family to `x = 1/2` and write `τ = sin t`. For `0 ≤ τ ≤ s` the spectral boundary is
`P = (s − τ)/(1 − τ)`, `E² = (1 + τ)(s − τ)` (67), and the objective is
`Φ_bal(1/2, t; δ) = F_δ(τ)` (68). Consequently the infimum of the symmetric honeycomb slice is
exactly `M₂(δ)`, and `κ_HC(δ) ≤ κ_bal(δ) ≤ M₂(δ)`.

**Formalization Note.** `0 ≤ τ = sin t ≤ s` is parametrized by `0 ≤ t ≤ arcsin s` (inside
`[0, π/2)`); (67)–(68) are identities for `P_bal`, `E_bal`, `Φ_bal` at `x = 1/2`, which are
defined also at `t = 0`. The **symmetric honeycomb slice** is the part of the feasible set of (9)
with `x = 1/2` and `η = ρ` (the proof's second paragraph, p.32); its infimum is the real `sInf`
of `Φ_HC` over it. -/
theorem proposition_6_5 (δ : ℝ) (hδ : 0 < δ) (hδ' : δ < 1 / 2) :
    (∀ t : ℝ, 0 ≤ t → t ≤ Real.arcsin (1 - 2 * δ) →
      Pbal (1 / 2) t δ = ((1 - 2 * δ) - Real.sin t) / (1 - Real.sin t) ∧
      Ebal (1 / 2) t δ ^ 2 = (1 + Real.sin t) * ((1 - 2 * δ) - Real.sin t) ∧
      PhiBal (1 / 2) t δ = Fdelta δ (Real.sin t)) ∧
    sInf {r : ℝ | ∃ η z : ℝ, InDHC (1 / 2) η η z ∧ 1 - 2 * δ < GammaHC (1 / 2) η η z ∧
      r = PhiHC (1 / 2) η η z} = M2 δ ∧
    kappaHC δ ≤ kappaBal δ ∧ kappaBal δ ≤ M2 δ := by sorry

end HoneycombCodes
