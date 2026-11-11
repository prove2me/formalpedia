-- Prove2me | Theorems.Thm_GaussDiffSVP_theorem_9_1
-- name    : GaussDiffSVP.theorem_9_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T22:03:09.534311+00:00
-- url     : https://prove2.me/theorems/1d3553b3-951d-4dd6-a598-b638d35dac0e
-- title:
--   Theorem 9.1 — affine target representations: $\mu_\delta = V(eE/4)^{n/2}e^{\pm O(\ell_n)}$ and the variance bound
-- statement:
--   Take the SVP setting of Section 9: a full-rank rational $L = B\mathbb Z^n$, a scale $Q$ with $Q\le\lambda_1(L)^2<(1+1/n)Q$, $p$ and $s$ from Proposition 3.6, the uniform line $\Gamma = L+\mathbb ZBv/p$, $K = p^{-1}L$, $r = \sqrt2s$, $V = r^n/\det\Gamma$, a fixed shortest vector $v_*$, $z$ uniform in $K/L$ independent of the line, a fixed $\delta\in(L/2)/L$, the coset $C = z+\delta+\Gamma$, and for a child energy $a$, $E = 4a-c$ with $c = 2^{2\kappa_{\mathrm{pack}}-1}/e$ and
--   $$J_C(v_*) = \sum_{x\in C}\mathbf 1_{S_r(a)}(x)\mathbf 1_{S_r(a)}(x-v_*).$$
--   Let $a$ range over a fixed compact set with $E-2/e$ bounded below by a positive constant, and $\mu_\delta = \mathbb E_{\Gamma,z}[J_C(v_*)]$. Uniformly in $\delta$:
--   $$\mu_\delta = V(eE/4)^{n/2}\exp(\pm O(\ell_n)),\qquad\frac{\mathrm{Var}_{\Gamma,z}J_C(v_*)}{\mu_\delta^2}\le\frac1{\mu_\delta}+2^{-h_n+O(\ell_n)},$$
--   and for every fixed $\Gamma$, $\mathbb E_z[J_C(v_*)\mid\Gamma] = \mu_\delta$. Averaging over a random coset lowers the bridge threshold from $E>1$ to $E>2/e$.
--
--   Differences from the source:
--   - generalization: $p$, $s$ from Proposition 3.6 → every $s$ with $s^2$ rational within relative error $C_s/n$ and every prime in the window $[c_1X,c_2X]$, for every fixed $C_s$, $c_1\le c_2$; reason: covers the prime and scale of Proposition 3.6
--   - encoding: $z\in K/L$, $\delta\in(L/2)/L$, the line → $z = p^{-1}B\bar y$ with $y$ uniform in $\mathbb F_p^n$; $\delta = \tfrac12B\bar e$; the uniform nonzero generator $v$; reason: same laws
--   - encoding: the variance bound (90) → $\mathbb E[J^2]\le\mu^2+\mu+2^{-h_n+C\ell_n}\mu^2$; reason: equivalent since $0<\mu_\delta<\infty$ by (89)
--   - reading: $O(\ell_n)$, uniformity in $\delta$ and on the range, large $n$ → one constant $C$ and $n_0$ fixed before $n$, $B$, $Q$, $s$, $p$, $v_*$, $a$, $\delta$; reason: uniformity as stated
--   - encoding: $\det\Gamma$; averages → $\det L/p$; sums in $[0,\infty]$ over equally likely outcomes divided by their number; reason: same values
-- source:
--   Gao–Han–Hu, Gaussian Difference Dynamics: Breaking the 2^{n/2} Barrier for the Shortest Vector Problem and Discrete Gaussian Sampling, arXiv:2611.04336 (held version, sha256 233bf8bb…0692), Theorem 9.1, p.42 (setting §9, pp.41–42)

import Mathlib
import Definitions.Def_SuperlatSVP_lat
import Definitions.Def_SuperlatSVP_indexExt
import Definitions.Def_GaussDiffSVP_svpBudget
import Definitions.Def_GaussDiffSVP_halfGrid
import Definitions.Def_GaussDiffSVP_cosetCount

open SuperlatSVP
open scoped ENNReal

namespace GaussDiffSVP

/-- Theorem 9.1 (Affine target representations) (Gao–Han–Hu, *Gaussian Difference Dynamics*, arXiv:2611.04336 (held version, sha256 233bf8bb…0692), p.42), in the setting of §9 (pp.41–42): the
full-rank rational lattice `L = Bℤⁿ`, a scale `Q` with `Q ≤ λ₁(L)² < (1 + 1/n)Q`, `p` and `s` from
Proposition 3.6, the uniform line `Γ = L + ℤBv/p` (`v` uniform nonzero in `𝔽_pⁿ`), `K = p⁻¹L`,
`r = √2 s`, `V = rⁿ/det Γ`, a fixed shortest vector `v_*` of `L`, `z` uniform in `K/L` independently of
the line, a fixed `δ ∈ (L/2)/L`, `C = z + δ + Γ` (86), and, for a child energy `a`, `E = 4a − c`,
`c = 2^{2κ_pack−1}/e`, `J_C(v_*) = ∑_{x ∈ C} 1_{S_r(a)}(x) 1_{S_r(a)}(x − v_*)` (88), `a` ranging over
a fixed compact set with `E − 2/e` bounded below by a positive constant. For each fixed `δ` let
`μ_δ = E_{Γ,z}[J_C(v_*)]`. Uniformly in `δ` (and on the range):

1. `μ_δ = V(eE/4)^{n/2} exp(±O(ℓ_n))` (89);
2. `Var_{Γ,z} J_C(v_*) / μ_δ² ≤ 1/μ_δ + 2^{−h_n + O(ℓ_n)}` (90);
3. for every fixed `Γ`, `E_z[J_C(v_*) | Γ] = μ_δ`.

**Formalization Note.** "`p, s` from Proposition 3.6": for every fixed `C_s` and window constants
`c₁ ≤ c₂`, uniformly over `s > 0` with `s²` rational, `|s² − 2πA_G Q/n| ≤ (C_s/n)(2πA_G Q/n)`
(`A_G = e/2^{2κ_pack}`), and every prime `p ∈ [c₁X, c₂X]`, `X = 2^{h_n} det L/sⁿ`. `z` is encoded as
`p⁻¹Bȳ` with `y` uniform in `𝔽_pⁿ`, `δ` as `½Bē` with `e ∈ (ℤ/2)ⁿ` (`halfGrid`), the line by its
generator `v` (see Proposition 3.6). `det Γ = det L/p`. Averages are sums in `ℝ≥0∞` divided by the
numbers `(pⁿ − 1)pⁿ` and `pⁿ` of equally likely outcomes. (90) is stated multiplied out,
`E[J²] ≤ μ² + μ + 2^{−h_n+Cℓ_n} μ²`, which is (90) since `μ_δ` is positive and finite by (89).
`h_n`, `ℓ_n`, `w_n` are the default schedule (163). -/
theorem theorem_9_1 :
    ∀ Cs c₁ c₂ : ℝ, 0 < Cs → 0 < c₁ → c₁ ≤ c₂ →
    ∀ Rng : Set ℝ, IsCompact Rng → Rng ⊆ Set.Ioi 0 → ∀ m : ℝ, 0 < m →
    (∀ a ∈ Rng, 2 / Real.exp 1 + m ≤
      4 * a - (2 : ℝ) ^ (2 * (401 / 1000 : ℝ) - 1) / Real.exp 1) →
    ∃ C : ℝ, ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n →
      ∀ B : Matrix (Fin n) (Fin n) ℚ, B.det ≠ 0 → ∀ Q s : ℝ, 0 < Q →
      Q ≤ lam1 (lat (B.map (↑))) ^ 2 → lam1 (lat (B.map (↑))) ^ 2 < (1 + 1 / (n : ℝ)) * Q →
      0 < s → (∃ q : ℚ, s ^ 2 = q) →
      |s ^ 2 - 2 * Real.pi * (Real.exp 1 / (2 : ℝ) ^ (2 * (401 / 1000 : ℝ))) * Q / n| ≤
        Cs / n * (2 * Real.pi * (Real.exp 1 / (2 : ℝ) ^ (2 * (401 / 1000 : ℝ))) * Q / n) →
      ∀ p : ℕ, p.Prime →
      c₁ * ((2 : ℝ) ^ svpBudget.h n * |(B.map ((↑) : ℚ → ℝ)).det| / s ^ n) ≤ p →
      (p : ℝ) ≤ c₂ * ((2 : ℝ) ^ svpBudget.h n * |(B.map ((↑) : ℚ → ℝ)).det| / s ^ n) →
      ∀ vs : E n, vs ∈ lat (B.map (↑)) → vs ≠ 0 → ‖vs‖ = lam1 (lat (B.map (↑))) →
      ∀ a ∈ Rng, ∀ e : Fin n → ZMod 2,
      let r := Real.sqrt 2 * s
      let V := r ^ n / (|(B.map ((↑) : ℚ → ℝ)).det| / p)
      let E := 4 * a - (2 : ℝ) ^ (2 * (401 / 1000 : ℝ) - 1) / Real.exp 1
      let J : (Fin n → ZMod p) → (Fin n → ZMod p) → ℝ≥0∞ := fun v y =>
        ((cosetCount (indexExt (B.map (↑)) p v)
          ((1 / (p : ℝ)) • vecE ((B.map ((↑) : ℚ → ℝ)).mulVec fun i => ((y i).val : ℝ)) +
            halfGrid (B.map (↑)) e) vs r (svpBudget.w n) a : ℕ∞) : ℝ≥0∞)
      let μ := (∑' v : {v : Fin n → ZMod p // v ≠ 0}, ∑' y : Fin n → ZMod p, J v y) /
        (((p : ℝ≥0∞) ^ n - 1) * (p : ℝ≥0∞) ^ n)
      (ENNReal.ofReal (V * (Real.exp 1 * E / 4) ^ ((n : ℝ) / 2) *
            Real.exp (-(C * svpBudget.ell n))) ≤ μ ∧
        μ ≤ ENNReal.ofReal (V * (Real.exp 1 * E / 4) ^ ((n : ℝ) / 2) *
            Real.exp (C * svpBudget.ell n))) ∧
      (∑' v : {v : Fin n → ZMod p // v ≠ 0}, ∑' y : Fin n → ZMod p, J v y ^ 2) /
          (((p : ℝ≥0∞) ^ n - 1) * (p : ℝ≥0∞) ^ n) ≤
        μ ^ 2 + μ + ENNReal.ofReal ((2 : ℝ) ^ (-svpBudget.h n + C * svpBudget.ell n)) * μ ^ 2 ∧
      ∀ v : Fin n → ZMod p, v ≠ 0 → (∑' y : Fin n → ZMod p, J v y) / (p : ℝ≥0∞) ^ n = μ := by sorry

end GaussDiffSVP
