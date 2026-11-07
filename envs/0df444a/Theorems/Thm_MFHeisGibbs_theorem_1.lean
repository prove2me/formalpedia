-- Prove2me | Theorems.Thm_MFHeisGibbs_theorem_1
-- name    : MFHeisGibbs.theorem_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T10:57:50.47819+00:00
-- url     : https://prove2.me/theorems/5a2c99b6-e9d4-42ef-9fb2-2e44405160a8
-- title:
--   Theorem 1 (Main theorem) — $\mathrm{gap}(-\mathcal L)=\Theta(1)$ for $\beta<2$, $\Theta(n^{-1/2})$ at $\beta=2$, $\Theta(n^{-1})$ for $\beta\in(2,\infty]$
-- statement:
--   On $n$ qubits, let $H_n=-\frac1n\sum_\alpha(S^\alpha_{\mathrm{tot}})^2$ be the mean-field Heisenberg Hamiltonian, and let $\mathcal L_C$, $\mathcal L_D$, $\mathcal L_{F,\sigma}$ be the coherent, Davies and operator-Fourier-transform Lindbladians built from single-site Pauli jumps. Here $f:\mathbb R\to\mathbb C$ is continuous with $f(\nu)=e^{-\nu/2}\overline{f(-\nu)}$, $|f|\le1$ and $c_\star=\inf_{\nu\le0}|f(\nu)|^2>0$ (condition (4)). Then for every such filter, every width $\sigma>0$ and every fixed $0\le\beta<\infty$, each of the three generators has a one-dimensional kernel $\mathbb CI$ and
--
--   $$\mathrm{gap}(-\mathcal L)=\begin{cases}\Theta(1),&\beta\in[0,2),\\\Theta(n^{-1/2}),&\beta=2,\\\Theta(n^{-1}),&\beta\in(2,\infty).\end{cases}$$
--
--   If moreover $f(0)=c_0$ and $\lim_{\nu\to-\infty}f(\nu)=c_-$ with $0<c_0\le c_-\le1$, then at $\beta=\infty$ the generators $\mathcal L_{C,\infty}$, $\mathcal L_{D,\infty}$, $\mathcal L_{F,\sigma,\infty}$ have a one-dimensional kernel and gap $\Theta(n^{-1})$.
--
--   Here $\Theta$ refers to $n\to\infty$ with $\beta,f,\sigma$ fixed: there are constants $c,C>0$, which may depend on those parameters, with $c\,n^{-a}\le\mathrm{gap}\le C\,n^{-a}$ for all $n\ge2$.
--
--   The theorem says that giving up exact energy resolution does not change how the relaxation time grows with the system size, at any temperature. It also settles the critical exponent, which was open even for the Davies generator.
--
--   **Formalization Note** At $\beta=0$ the OFT generator is the limit formula $\mathcal L_{F,\sigma,0}$, and at $\beta=\infty$ the generators are the explicit formulas (100), (101), (113); the milestone `eq_101_113_limits` shows these are the limits the page takes.
--
--   Differences from the source:
--   - reading: gap(−L), 'spectral gap of −L, Equation (27)' (p.43) → the spectral gap inf{−Re λ : λ ≠ 0 an eigenvalue} together with the clause ker L = ℂ·I, at every β; reason: the Rayleigh form degenerates at β = ∞, where the paper itself argues spectrally (p.39); with the scalar kernel this is at least as strong as (27), which is linked to it by the milestone eq_27
--   - reading: Θ(·) for fixed β → ∀ β, f, σ ∃ c, C > 0 ∀ n ≥ 2; reason: p.41 says Θ refers to n → ∞ with β, f, σ fixed; each gap is positive, so a bound for large n is a bound for all n ≥ 2
--   - reading: 'for the OFT construction we also get gap(−L_{F,σ,0}) = Θ(1) at the β = 0 point' → LFall, which is the formula LF0 at β = 0; reason: the printed ĝ_σ vanishes at β = 0, so literal (10) is the zero map; p.41 defines L_{F,σ,0} as the limit, stated in the milestone eq_101_113_limits
--   - reading: at β = 0 the page names only 'the Davies–Metropolis and the coherent generators' → L_D at β = 0 for every f with (4); reason: Theorem 1's first sentence covers 0 ≤ β ≤ ∞ and all three generators, and (44) at β = 0 gives every f
--   - encoding: generators at β = ∞ defined as norm limits → the explicit formulas (100), (101), (113), with f_∞(ad_{H_n}) for (100); reason: the page gives these; Fact 2.1 makes (100) equal to f_∞(ad_{H_n})(σ), and the limits are the milestone eq_101_113_limits
--   - encoding: K̂(ω) in (10) as a time integral or Bohr sum → the Bohr form of (11), expanded through the scalar integrals κ(ν, μ); reason: the page states the two equal; the integrand is bounded by a Gaussian for f with (4), so the expansion loses nothing
-- source:
--   Raikovich, Mák, Czabán, Gilyén, arXiv:2610.06818 (version dated November 3, 2026, sha256 164d57ba…), Theorem 1, p.5 (PDF 6), continued p.6 (PDF 7)

import Definitions.Def_MFHeisGibbs_Generators
import Definitions.Def_MFHeisGibbs_Gap

open Filter Topology

namespace MFHeisGibbs

/-- **Theorem 1 (Main theorem)**, Raikovich, Mák, Czabán, Gilyén, arXiv:2610.06818 (version dated November 3, 2026, sha256 164d57ba…), p.5 (continued on p.6).
For every KMS filter `f` (4), every width `σ = s > 0` and every `0 ≤ β < ∞`, the Lindbladians
`L_C`, `L_D`, `L_{F,σ}` have `gap(−L) = Θ(1)` for `β < 2`, `Θ(n^{−1/2})` at `β = 2`, `Θ(n^{−1})` for
`β > 2`. At `β = ∞`, under `f(0) = c₀`, `lim_{ν→−∞} f(ν) = c₋`, `0 < c₀ ≤ c₋ ≤ 1`, the gap is `Θ(n^{−1})`.

**Formalization Note.** `Θ` is read as on p.41: the constants come after `β, f, σ` and before `n`, for
all `n ≥ 2`. `gap` is the spectral gap `specGap` with a scalar kernel (`GapOrder`). At `β = 0` the OFT
generator is `LF0` (`LFall`), and at `β = ∞` the generators are the formulas (100), (101), (113); the
milestone `eq_101_113_limits` states both are the limits the page takes. -/
theorem theorem_1 :
    (∀ f : ℝ → ℂ, IsKMSFilter f → ∀ s : ℝ, 0 < s → ∀ β : ℝ, 0 ≤ β →
      GapOrder (LC β f) (phase β) ∧ GapOrder (LD β f) (phase β) ∧
        GapOrder (LFall β s f) (phase β)) ∧
    (∀ (f : ℝ → ℂ) (c₀ cm : ℝ), IsKMSFilter f → f 0 = c₀ → Tendsto f atBot (𝓝 (cm : ℂ)) →
      0 < c₀ → c₀ ≤ cm → cm ≤ 1 → ∀ s : ℝ, 0 < s →
      GapOrder (LCinf c₀ cm) 1 ∧ GapOrder (LDinf c₀ cm) 1 ∧
        GapOrder (LFinf cm (bSigma s f)) 1) := by sorry

end MFHeisGibbs
