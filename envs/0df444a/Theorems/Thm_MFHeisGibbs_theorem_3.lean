-- Prove2me | Theorems.Thm_MFHeisGibbs_theorem_3
-- name    : MFHeisGibbs.theorem_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T10:57:41.542914+00:00
-- url     : https://prove2.me/theorems/25f2ade2-9187-4226-a67c-4788450544ff
-- title:
--   Theorem 3 — at $\beta=\infty$: unique stationary state $\rho_\infty$, $\mathrm{gap}=\Theta(n^{-1})$, $t_{\mathrm{mix}}(\varepsilon)=\Theta(n\log(1/\varepsilon))$
-- statement:
--   For $n\ge2$ and $\mathcal L\in\{\mathcal L_{C,\infty},\mathcal L_{D,\infty},\mathcal L_{F,\sigma,\infty}\}$, the unique stationary state is $\rho_\infty=\Pi_J/(n+1)$, and
--
--   $$\mathrm{gap}(-\mathcal L)=\Theta(n^{-1}),\qquad t_{\mathrm{mix},\mathcal L}(\varepsilon)=\Theta\big(n\log(1/\varepsilon)\big)\quad(0<\varepsilon\le1/4).$$
--
--   For the coherent and Davies generators the implicit constants depend only on $c_0$, uniformly over $c_-\in[c_0,1]$. For the OFT generator they depend only on $f$ and $\sigma$.
--
--   This is the zero-temperature end of the phase diagram, with convergence in trace norm.
--
--   Differences from the source:
--   - encoding: ρ_∞ = Π_J/(n+1), with Π_J the spin-n/2 block → ρ_∞ the normalized ground projection, with the clause Tr Π = n + 1; reason: the ground space of H_n is the spin-n/2 block, by (32), and p.3 defines the state as maximally mixed on it
--   - encoding: L_{C,∞}, L_{D,∞}, L_{F,σ,∞} as limits → the explicit formulas (100), (101), (113); reason: the page gives these formulas; the limits are the milestone eq_101_113_limits
-- source:
--   Raikovich, Mák, Czabán, Gilyén, arXiv:2610.06818 (version dated November 3, 2026, sha256 164d57ba…), Theorem 3, p.36 (PDF 37)

import Definitions.Def_MFHeisGibbs_Generators
import Definitions.Def_MFHeisGibbs_Gap
import Definitions.Def_MFHeisGibbs_Mixing

open Filter Topology Matrix

namespace MFHeisGibbs

/-- **Theorem 3 (Zero-temperature gap and mixing)**, Raikovich, Mák, Czabán, Gilyén, arXiv:2610.06818 (version dated November 3, 2026, sha256 164d57ba…), p.36.
For `n ≥ 2` and `L ∈ {L_{C,∞}, L_{D,∞}, L_{F,σ,∞}}`, the unique stationary state is `ρ_∞`,
`gap(−L) = Θ(n^{−1})`, `t_{mix,L}(ε) = Θ(n log(1/ε))` for `0 < ε ≤ 1/4`. For the coherent and Davies
generators the constants depend only on `c₀`, uniformly over `c₋ ∈ [c₀, 1]`; for the OFT generator, only
on `f` and `σ`. Also `ρ_∞ = Π_J/(n+1)`.

**Formalization Note.** `rhoInf n` is the maximally mixed state on the ground space (p.3); `Tr Π_J = n + 1`
is the clause giving the page's form. The generators are the explicit formulas (101), (113). -/
theorem theorem_3 :
    (∀ n : ℕ, 2 ≤ n → trace (groundProj n) = (n : ℂ) + 1) ∧
    (∀ c₀ : ℝ, 0 < c₀ → c₀ ≤ 1 → ∃ c > 0, ∃ C > 0, ∀ cm : ℝ, c₀ ≤ cm → cm ≤ 1 → ∀ n : ℕ, 2 ≤ n →
      ZeroTempBounds c C (LCinf c₀ cm n) ∧ ZeroTempBounds c C (LDinf c₀ cm n)) ∧
    (∀ (f : ℝ → ℂ) (c₀ cm : ℝ), IsKMSFilter f → f 0 = c₀ → Tendsto f atBot (𝓝 (cm : ℂ)) →
      0 < c₀ → c₀ ≤ cm → cm ≤ 1 → ∀ s : ℝ, 0 < s → ∃ c > 0, ∃ C > 0, ∀ n : ℕ, 2 ≤ n →
        ZeroTempBounds c C (LFinf cm (bSigma s f) n)) := by sorry

end MFHeisGibbs
