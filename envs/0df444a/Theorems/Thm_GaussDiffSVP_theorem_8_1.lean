-- Prove2me | Theorems.Thm_GaussDiffSVP_theorem_8_1
-- name    : GaussDiffSVP.theorem_8_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T22:02:14.145409+00:00
-- url     : https://prove2.me/theorems/27984ff7-b28c-4e42-84db-aa325cb6dc7d
-- title:
--   Theorem 8.1 — midpoint lens moments $\mathbb E_d[J_d(z)] = e^{\pm\eta_n}B$, $\mathbb E_d[J_d(z)J_d(z')]\le e^{\eta_n}B^2$
-- statement:
--   Let $(a,b)$ range over a fixed compact subset of $(0,\infty)^2$ with $E = 4a-b\ge1+\kappa$ for a fixed $\kappa>0$. Assume (11) with $\varepsilon_n\to0$ for $\Gamma$ and $s$, and let $r = \sqrt2 s$, $w = w_n$. There is a constant $C$ depending only on the range and $\kappa$ such that, uniformly over the range, for all sufficiently large $n$, with $\eta_n = C(nw+\log(n+2))$ and $B = V_r(eE/4)^{n/2}$,
--   $$e^{-\eta_n}B\le\mathbb E_d[J_d(z)]\le e^{\eta_n}B,\qquad\mathbb E_d[J_d(z)J_d(z')]\le e^{\eta_n}B^2,$$
--   uniformly over $z,z'$ in the same parent coset $p+\Gamma$ and output shell $S_r(b)$, including $z = z'$, with the same $d$ in both copies. Here $J_d(z)$ counts pairs $z = x-y$ with $x\in(p/2+d+\Gamma)\cap S_r(a)$ and $y\in(-p/2+d+\Gamma)\cap S_r(a)$ and $d$ is uniform on $(\Gamma/2)/\Gamma$. These are the geometric inputs (27)–(28) of Theorem 4.3 for full differencing.
--
--   Differences from the source:
--   - encoding: $\mathbb E_d$ over $d\sim\mathrm{Unif}((\Gamma/2)/\Gamma)$ → average over the $2^n$ representatives $\tfrac12B\bar e$; reason: same law
--   - reading: $w$ → $w_n$ of the default schedule (163); reason: Section 8 sets $w = w_n$
--   - reading: $C$ depending only on the range and $\kappa$; $\varepsilon_n\to0$; large $n$ → $\exists C$ after the range and $\kappa$; then every sequence $\varepsilon_n\to0$; then $n_0$; reason: uniformity as stated
--   - encoding: counts and averages → values in $[0,\infty]$; reason: nonnegative
-- source:
--   Gao–Han–Hu, Gaussian Difference Dynamics: Breaking the 2^{n/2} Barrier for the Shortest Vector Problem and Discrete Gaussian Sampling, arXiv:2611.04336 (held version, sha256 233bf8bb…0692), Theorem 8.1, p.39 (setting §8.1, p.38)

import Mathlib
import Definitions.Def_SuperlatSVP_lat
import Definitions.Def_RegevLWE_GaussConv_Lattice
import Definitions.Def_GaussDiffSVP_svpBudget
import Definitions.Def_GaussDiffSVP_shell
import Definitions.Def_GaussDiffSVP_volFactor
import Definitions.Def_GaussDiffSVP_halfGrid
import Definitions.Def_GaussDiffSVP_lensCount

open Filter Topology SuperlatSVP
open scoped ENNReal

namespace GaussDiffSVP

/-- Theorem 8.1 (Midpoint lens moments) (Gao–Han–Hu, *Gaussian Difference Dynamics*, arXiv:2611.04336 (held version, sha256 233bf8bb…0692), p.39). Let `(a, b)` range over a fixed compact subset
of `(0, ∞)²` satisfying `E = 4a − b ≥ 1 + κ` (71) for a fixed `κ > 0`. Under (11) with `ε_n → 0`
(`Γ = Bℤⁿ`, `ρ_{1/s}(Γ*∖{0}) ≤ ε_n`), with `r = √2 s` and `w = w_n`, the following hold uniformly over
this range for all sufficiently large `n`. There is a constant `C` depending only on the range and
`κ` such that, with `η_n = C(n w + log(n + 2))` and `B = V_r(eE/4)^{n/2}`,
`e^{−η_n}B ≤ E_d[J_d(z)] ≤ e^{η_n}B` (75) and `E_d[J_d(z)J_d(z′)] ≤ e^{η_n}B²` (76), where the
second estimate uses the same `d` in both copies and is uniform over `z, z′` in the same parent coset
`p + Γ` and output shell `S_r(b)`, including `z = z′`.

**Formalization Note.** `J_d(z)` is `lensCount`; `E_d` is the uniform average over the `2ⁿ` half-grid
representatives `d = ½Bē`, `e ∈ (ℤ/2)ⁿ` (`halfGrid`). `w_n` is the default schedule (163) ("set
`w = w_n`", p.38). Quantifiers: range and `κ`, then `C`, then the sequence `ε_n`, then `n₀`, then `n`,
`Γ`, `s`, `(a, b)`, `p`, `z`, `z′`. Counts and averages are in `ℝ≥0∞`. -/
theorem theorem_8_1 :
    ∀ Rng : Set (ℝ × ℝ), IsCompact Rng → Rng ⊆ Set.Ioi 0 ×ˢ Set.Ioi 0 →
    ∀ κ : ℝ, 0 < κ → (∀ ab ∈ Rng, 1 + κ ≤ 4 * ab.1 - ab.2) →
    ∃ C : ℝ, 0 < C ∧ ∀ ε : ℕ → ℝ, Tendsto ε atTop (𝓝 0) → ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n →
      ∀ B : Matrix (Fin n) (Fin n) ℝ, B.det ≠ 0 → ∀ s : ℝ, 0 < s →
      rhoSet (1 / s) {y | y ∈ RegevLWE.GaussConv.dual (lat B) ∧ y ≠ 0} ≤ ENNReal.ofReal (ε n) →
      let r := Real.sqrt 2 * s
      let w := svpBudget.w n
      let η := C * (n * w + Real.log (n + 2))
      ∀ ab ∈ Rng,
      let Bv := volFactor B r * (Real.exp 1 * (4 * ab.1 - ab.2) / 4) ^ ((n : ℝ) / 2)
      ∀ p z z' : E n, z - p ∈ lat B → z ∈ shell r w ab.2 → z' - p ∈ lat B → z' ∈ shell r w ab.2 →
        (ENNReal.ofReal (Real.exp (-η) * Bv) ≤
            ∑ e : Fin n → ZMod 2, ((lensCount (lat B) r w ab.1 p (halfGrid B e) z : ℕ∞) : ℝ≥0∞) /
              (2 : ℝ≥0∞) ^ n ∧
          ∑ e : Fin n → ZMod 2, ((lensCount (lat B) r w ab.1 p (halfGrid B e) z : ℕ∞) : ℝ≥0∞) /
              (2 : ℝ≥0∞) ^ n ≤ ENNReal.ofReal (Real.exp η * Bv)) ∧
        ∑ e : Fin n → ZMod 2, ((lensCount (lat B) r w ab.1 p (halfGrid B e) z : ℕ∞) : ℝ≥0∞) *
            ((lensCount (lat B) r w ab.1 p (halfGrid B e) z' : ℕ∞) : ℝ≥0∞) / (2 : ℝ≥0∞) ^ n ≤
          ENNReal.ofReal (Real.exp η * Bv ^ 2) := by sorry

end GaussDiffSVP
