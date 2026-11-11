-- Prove2me | Theorems.Thm_GaussDiffSVP_theorem_8_2
-- name    : GaussDiffSVP.theorem_8_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T22:02:41.44939+00:00
-- url     : https://prove2.me/theorems/98487379-c0e4-48d4-ae8a-d838f5c9e569
-- title:
--   Theorem 8.2 — full difference trees: $e^{\pm\varepsilon_j}A_j$ moment bounds and $\varepsilon_d = o(n)$
-- statement:
--   Let the depth $d$ be fixed, the energies $a_0,\dots,a_d$ lie in a fixed compact positive range, and assume the smoothing assumption of Theorem 8.1 ($r = \sqrt2s$, $w = w_n$). With $A_0>0$, $E_j = 4a_{j-1}-a_j$, $B_j = V_r(eE_j/4)^{n/2}$ and $A_j = A_{j-1}^2B_j$, suppose constants $\kappa,\zeta>0$ satisfy
--   $$E_j\ge1+\kappa,\qquad A_{j-1}B_j\ge2^{\zeta n}$$
--   at every height. Assume each leaf satisfies $\mathcal C(A_0\mathbf 1_{(p+\Gamma)\cap S_r(a_0)},\varepsilon_0)$ uniformly in its offset, with $\varepsilon_0 = o(n)$. Then for sufficiently large $n$, each height-$j$ list of Algorithm 3 at offset $p$ satisfies, for $z,z'$ in its coset and shell,
--   $$e^{-\varepsilon_j}A_j\le m_{j,p}(z)\le e^{\varepsilon_j}A_j,\qquad S^{\mathrm{act}}_{j,p}(z,z')\le e^{\varepsilon_j}A_j^2,$$
--   where $\varepsilon_j = 2\varepsilon_{j-1}+\eta_n+\log(1+2/(A_{j-1}B_j))$ and $\eta_n = C(nw_n+\log(n+2))$, and
--   $$\varepsilon_d\le2^d\varepsilon_0+(2^d-1)\eta_n+2(2^d-1)2^{-\zeta n} = o(n).$$
--   Each full layer squares the count at a location and multiplies it by the number of midpoints, which is what creates enough target representations for SVP.
--
--   Differences from the source:
--   - generalization: leaves are cooling roots $\mathrm{BuildIdeal}(p,0)$ → any leaf law satisfying the leaf bound; reason: the theorem assumes only the leaf moment bound; Algorithm 3 is the instance
--   - reading: the constant $C$ of $\eta_n$ → $\exists C$ after the range and $\kappa$, before $d$, $\zeta$ and the sequences; reason: it is Theorem 8.1's constant
--   - encoding: $\varepsilon_0 = o(n)$; $= o(n)$ in (84) → a nonnegative sequence with $\varepsilon_0(n)/n\to0$; a separate limit statement for the right side of (84); reason: explicit quantifiers
--   - encoding: conditional on the prescribed offset and ancestor assignments → the law of the height-$j$ node at offset $p$; reason: the tree law given its offset
--   - reading: $w$, the smoothing assumption → $w_n$ of (163); $\rho_{1/s}(\Gamma^*\setminus\{0\})\le\varepsilon_n\to0$; reason: the setting of Theorem 8.1
--   - generalization: the leaf intensity $A_0 = (\Upsilon_0/V_r)e^{-na_0/2}$ of (79) → any $A_0>0$; reason: the theorem uses $A_0$ only through the leaf bound and the recursion (79), (81); the value of (79) is an instance
-- source:
--   Gao–Han–Hu, Gaussian Difference Dynamics: Breaking the 2^{n/2} Barrier for the Shortest Vector Problem and Discrete Gaussian Sampling, arXiv:2611.04336 (held version, sha256 233bf8bb…0692), Theorem 8.2, p.40 ((79), Algorithm 3, p.40)

import Mathlib
import Definitions.Def_SuperlatSVP_lat
import Definitions.Def_RegevLWE_GaussConv_Lattice
import Definitions.Def_GaussDiffSVP_svpBudget
import Definitions.Def_GaussDiffSVP_shell
import Definitions.Def_GaussDiffSVP_volFactor
import Definitions.Def_GaussDiffSVP_InClassC
import Definitions.Def_GaussDiffSVP_fullTreeLaw
import Definitions.Def_GaussDiffSVP_nomIntensity
import Definitions.Def_GaussDiffSVP_fullErr

open Filter Topology SuperlatSVP
open scoped ENNReal

namespace GaussDiffSVP

/-- Theorem 8.2 (Full difference trees) (Gao–Han–Hu, *Gaussian Difference Dynamics*, arXiv:2611.04336 (held version, sha256 233bf8bb…0692), p.40). Let the depth `d` be fixed, the energies
`a_0, …, a_d` lie in a fixed compact positive range, and assume the smoothing assumption of
Theorem 8.1 (`Γ = Bℤⁿ`, `ρ_{1/s}(Γ*∖{0}) ≤ ε_n → 0`, `r = √2 s`, `w = w_n`). With
`A_0` given, `E_j = 4a_{j−1} − a_j`, `B_j = V_r(eE_j/4)^{n/2}` and `A_j = A_{j−1}²B_j` (79), suppose
constants `κ, ζ > 0` satisfy `E_j ≥ 1 + κ` and `A_{j−1}B_j ≥ 2^{ζn}` at every height (81). Assume each
leaf satisfies `C(A_0 1_{(p+Γ)∩S_r(a_0)}, ε_0)` uniformly in its prescribed offset, with
`ε_0 = o(n)`, and use independent private randomness in disjoint subtrees (Algorithm 3). Then for
sufficiently large `n` each height-`j` list, conditional on its prescribed offset, satisfies
`e^{−ε_j}A_j ≤ m_{j,p}(z) ≤ e^{ε_j}A_j` and `S_{j,p}^{act}(z, z′) ≤ e^{ε_j}A_j²` (82) for `z, z′` in its
prescribed coset and shell, where `ε_j = 2ε_{j−1} + η_n + log(1 + 2/(A_{j−1}B_j))` and
`η_n = C(n w_n + log(n + 2))` (83). The root error obeys
`ε_d ≤ 2^d ε_0 + (2^d − 1)η_n + 2(2^d − 1)2^{−ζn} = o(n)` (84).

**Formalization Note.** `C` is the constant of Theorem 8.1, depending only on the range and `κ`; it is
quantified after them and before `d`, `ζ` and the sequences. The tree is `fullTreeLaw` (Algorithm 3)
over an **arbitrary** leaf law satisfying the leaf bound (Algorithm 3's leaves are cooling roots,
`buildIdealLaw`); "conditional on its prescribed offset and ancestor assignments" is the law of
the node of height `j` at offset `p`. `ε_0 = o(n)` is a nonnegative sequence with `ε_0(n)/n → 0`;
"`= o(n)`" in (84) is the separate conclusion that the right-hand side divided by `n` tends to `0`.
`A_0 > 0` is arbitrary. Moments are in `ℝ≥0∞`; `A_j`, `B_j`, `ε_j` are the real recursions
`nomIntensity` and `fullErr`. -/
theorem theorem_8_2 :
    ∀ Rng : Set ℝ, IsCompact Rng → Rng ⊆ Set.Ioi 0 → ∀ κ : ℝ, 0 < κ →
    ∃ C : ℝ, 0 < C ∧ ∀ d : ℕ, ∀ ζ : ℝ, 0 < ζ →
    ∀ ε : ℕ → ℝ, Tendsto ε atTop (𝓝 0) →
    ∀ ε₀ : ℕ → ℝ, (∀ n, 0 ≤ ε₀ n) → Tendsto (fun n : ℕ => ε₀ n / n) atTop (𝓝 0) →
      Tendsto (fun n : ℕ => ((2 : ℝ) ^ d * ε₀ n +
          ((2 : ℝ) ^ d - 1) * (C * (n * svpBudget.w n + Real.log (n + 2))) +
          2 * ((2 : ℝ) ^ d - 1) * (2 : ℝ) ^ (-(ζ * n))) / n) atTop (𝓝 0) ∧
      ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n →
      ∀ B : Matrix (Fin n) (Fin n) ℝ, B.det ≠ 0 → ∀ s : ℝ, 0 < s →
      rhoSet (1 / s) {y | y ∈ RegevLWE.GaussConv.dual (lat B) ∧ y ≠ 0} ≤ ENNReal.ofReal (ε n) →
      let r := Real.sqrt 2 * s
      let w := svpBudget.w n
      let ηn := C * (n * w + Real.log (n + 2))
      ∀ a : ℕ → ℝ, (∀ j, j ≤ d → a j ∈ Rng) → ∀ A₀ : ℝ, 0 < A₀ →
      let Bf : ℕ → ℝ := fun j =>
        volFactor B r * (Real.exp 1 * (4 * a (j - 1) - a j) / 4) ^ ((n : ℝ) / 2)
      let A := nomIntensity A₀ Bf
      (∀ j, 1 ≤ j → j ≤ d → 1 + κ ≤ 4 * a (j - 1) - a j ∧ (2 : ℝ) ^ (ζ * n) ≤ A (j - 1) * Bf j) →
      ∀ leaf : E n → PMF (List (E n)),
        (∀ p, InClassC (leaf p)
          (Set.indicator {x | x - p ∈ lat B ∧ x ∈ shell r w (a 0)} fun _ => ENNReal.ofReal A₀)
          (ε₀ n)) →
        let εj := fullErr (ε₀ n) ηn A Bf
        (∀ j, j ≤ d → ∀ p z z' : E n,
          z - p ∈ lat B → z ∈ shell r w (a j) → z' - p ∈ lat B → z' ∈ shell r w (a j) →
          ENNReal.ofReal (Real.exp (-εj j) * A j) ≤ intensity (fullTreeLaw B r w a leaf j p) z ∧
          intensity (fullTreeLaw B r w a leaf j p) z ≤ ENNReal.ofReal (Real.exp (εj j) * A j) ∧
          factMoment (fullTreeLaw B r w a leaf j p) z z' ≤
            ENNReal.ofReal (Real.exp (εj j) * A j ^ 2)) ∧
        εj d ≤ (2 : ℝ) ^ d * ε₀ n + ((2 : ℝ) ^ d - 1) * ηn +
          2 * ((2 : ℝ) ^ d - 1) * (2 : ℝ) ^ (-(ζ * n)) := by sorry

end GaussDiffSVP
