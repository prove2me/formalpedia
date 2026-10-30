-- Prove2me | Theorems.Thm_HorodeckiBoundKey_corner_trace_norm
-- name    : HorodeckiBoundKey.corner_trace_norm
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T03:17:17.429197+00:00
-- url     : https://prove2.me/theorems/367be0f9-db83-4ce8-af74-c20b17c76a5c
-- title:
--   Eq. (13): the trace norm of the off-diagonal block of $\rho'$
-- statement:
--   Let $d\ge 2$, $l\ge 1$, $n\ge 1$ and $0<p\le\frac12$, and let $X = [\frac p2(\tau_1-\tau_0)]^{\otimes n}/N$ be the upper-right ($\langle 00|\cdot|11\rangle$) block of the state $\rho'$ of (12). Then
--   $$
--   \|X\|_1 = \frac12\Big(1-\frac1{2^l}\Big)^n\,\frac{1}{1+\big(\frac{1-2p}{2p}\big)^n}.
--   $$
--
--   This is the quantity the paper checks to tend to $1/2$, the value of the off-diagonal block of a private bit.
--
--   **Formalization Note** $\|\cdot\|_1$ is the trace norm $\mathrm{Tr}\sqrt{X^\dagger X}$ (`QAlgorithms.traceNorm`); the right-hand side is `cornerNormValue p l n`.
--
--   Differences from the source:
--   - reading: τ₂ in the left-hand side of (13) → τ₀; reason: τ₂ is defined nowhere in the paper, and (10), (11) and (12) all have τ₁ − τ₀
--   - encoding: the parameters of (11)–(13), left implicit → d ≥ 2, l ≥ 1, n ≥ 1, 0 < p ≤ 1/2; reason: ϱ_a of (9) needs d ≥ 2, (11) is a state only for 0 ≤ p ≤ 1/2, and the right-hand side of (13) divides by 2p; the conditions exclude only undefined cases
-- source:
--   Horodecki, Horodecki, Horodecki, Oppenheim, Secure key from bound entanglement, arXiv:quant-ph/0309110v2, eq. (13), p.3

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P24
import Definitions.Def_QAlgorithms_Papers_Independent_Gap48_P42
import Definitions.Def_HorodeckiBoundKey_recurrenceOutput
import Definitions.Def_HorodeckiBoundKey_cornerNormValue

open QAlgorithms QAlgorithms.Papers.Independent
open QAlgorithms.Papers.Independent.Information100.P21 (Op)
open scoped Matrix ComplexOrder ENNReal
open QAlgorithms.Papers.Independent.Dependency50.P24 (keyBlock)

namespace HorodeckiBoundKey

/-- Horodecki, Horodecki, Horodecki, Oppenheim, arXiv:quant-ph/0309110v2, eq. (13), p.3: "we
check that the trace norm of off-diagonal block ‖X‖ tends to 1/2:
‖[p/2 (τ₁ − τ₂)]^{⊗n}/N‖ = 1/2 (1 − 1/2^l)ⁿ 1/(1 + ((1−2p)/(2p))ⁿ)".

For `d ≥ 2`, `l ≥ 1`, `n ≥ 1` and `0 < p ≤ 1/2`, the trace norm of the `⟨00|·|11⟩` block
`X = [p/2 (τ₁ − τ₀)]^{⊗n}/N` of the state `ρ′` of (12) equals
`½ (1 − 2^{-l})ⁿ / (1 + ((1 − 2p)/(2p))ⁿ)` (`cornerNormValue p l n`).

**Formalization Note.** The page's `τ₂` is read as `τ₀`: `τ₂` is defined nowhere, and (10)–(12)
all have `τ₁ − τ₀`. The norm is the trace norm (`QAlgorithms.traceNorm`, `Tr √(X†X)`), as the
sentence before (13) says. `keyBlock ρ (0,0) (1,1)` is the upper-right block `X` (rows `|00⟩`,
columns `|11⟩`). -/
theorem corner_trace_norm (p : ℝ) (d l n : ℕ) (hd : 2 ≤ d) (hl : 1 ≤ l) (hn : 1 ≤ n)
    (hp0 : 0 < p) (hp : p ≤ 1 / 2) :
    traceNorm (keyBlock (recurrenceOutput p d l n) (0,0) (1,1)) =
      cornerNormValue p l n := by sorry

end HorodeckiBoundKey
