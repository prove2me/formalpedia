-- Prove2me | Theorems.Thm_MFHeisGibbs_eq_101_113_limits
-- name    : MFHeisGibbs.eq_101_113_limits
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T10:57:49.158002+00:00
-- url     : https://prove2.me/theorems/5616e958-5001-47ba-a708-28d1bf499e95
-- title:
--   (101), (113), and the $\beta\to0^+$ display — the generators at $\beta=\infty$ and OFT at $\beta=0$ are limits
-- statement:
--   Let $f$ satisfy (4), with $f(0)=c_0$, $\lim_{\nu\to-\infty}f(\nu)=c_-$, $0<c_0\le c_-\le1$, and let $\sigma>0$ and $n\ge2$. Then, as $\beta\to\infty$,
--
--   $$\mathcal L_{C,\beta}\to\mathcal L_{C,\infty},\quad\mathcal L_{D,\beta}\to\mathcal L_{D,\infty},\quad\mathcal L_{F,\sigma,\beta}\to\mathcal L_{F,\sigma,\infty}.$$
--
--   For any $f$ satisfying (4), as $\beta\to0^+$,
--
--   $$\mathcal L_{F,\sigma,\beta}[X]\to\mathcal L_{F,\sigma,0}[X]=b_\sigma\sum_{i,\alpha}(\sigma^{(i,\alpha)}X\sigma^{(i,\alpha)}-X).$$
--
--   This justifies the explicit generators in the main theorem at the two endpoints of the phase diagram.
--
--   Differences from the source:
--   - encoding: norm limits of the generators (in the Schrödinger picture for (101), (113)) → Tendsto at every X, for the Heisenberg-picture generators; reason: on a finite-dimensional space pointwise and norm convergence agree, and taking the Hilbert–Schmidt adjoint preserves the limit
-- source:
--   Raikovich, Mák, Czabán, Gilyén, arXiv:2610.06818 (version dated November 3, 2026, sha256 164d57ba…), (101), p.36 (PDF 37); (113), p.40 (PDF 41); the β → 0⁺ display, p.41 (PDF 42)

import Definitions.Def_MFHeisGibbs_Generators

open Filter Topology

namespace MFHeisGibbs

/-- **(101), (113) and the `β → 0⁺` display**, Raikovich, Mák, Czabán, Gilyén, arXiv:2610.06818 (version dated November 3, 2026, sha256 164d57ba…), pp.36, 40–41.
Under the hypotheses of §7, `L_{C,β} → L_{C,∞}`, `L_{D,β} → L_{D,∞}`, `L_{F,σ,β} → L_{F,σ,∞}` as
`β → ∞`; for a filter with (4), `L_{F,σ,β} → L_{F,σ,0}` as `β → 0⁺`.

**Formalization Note.** On the finite-dimensional `Op n`, convergence at every `X` is norm convergence of
the generator. This is what ties the explicit generators of the goal at `β = 0` and `β = ∞` to the
finite-temperature formulas. -/
theorem eq_101_113_limits :
    (∀ (f : ℝ → ℂ) (c₀ cm : ℝ), IsKMSFilter f → f 0 = c₀ → Tendsto f atBot (𝓝 (cm : ℂ)) →
      0 < c₀ → c₀ ≤ cm → cm ≤ 1 → ∀ s : ℝ, 0 < s → ∀ (n : ℕ), 2 ≤ n → ∀ X : Op n,
        Tendsto (fun β : ℝ => LC β f n X) atTop (𝓝 (LCinf c₀ cm n X)) ∧
        Tendsto (fun β : ℝ => LD β f n X) atTop (𝓝 (LDinf c₀ cm n X)) ∧
        Tendsto (fun β : ℝ => LF β s f n X) atTop (𝓝 (LFinf cm (bSigma s f) n X))) ∧
    (∀ f : ℝ → ℂ, IsKMSFilter f → ∀ s : ℝ, 0 < s → ∀ (n : ℕ), 2 ≤ n → ∀ X : Op n,
        Tendsto (fun β : ℝ => LF β s f n X) (𝓝[>] 0) (𝓝 (LF0 s f n X))) := by sorry

end MFHeisGibbs
