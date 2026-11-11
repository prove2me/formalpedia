-- Prove2me | Theorems.Thm_GaussDiffSVP_lemma_5_1
-- name    : GaussDiffSVP.lemma_5_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T22:03:35.741265+00:00
-- url     : https://prove2.me/theorems/b1f9a12b-ba06-45cc-ac04-e6e88875396e
-- title:
--   Lemma 5.1 — $B_j = 2^{-(J(a_0)+P(u))n+O(nw_n)}$, midpoint mass $V_{r/\sqrt2}(1\pm\eta_{\mathrm{mid}})$, degrees $\le D_j^+$
-- statement:
--   In the cooling setting — $u\in(1/2,31/50]$, $a_0 = 1/(1+u)$, $a_1 = 4a_0-2$, $\gamma^2 = 2(1-u)$, a full-rank $\Gamma = B\mathbb Z^n$ and $s$ with $\epsilon_\Gamma = \rho_{1/s}(\Gamma^*\setminus\{0\})\le2^{-h_n/3}$, $r_0 = \sqrt2 s$ — uniformly over (39) with $\gamma^2\le1-w_n/4$ and for all sufficiently large $n$:
--
--   1. $B_j = 2^{-(J(a_0)+P(u))n+O(nw_n)}$;
--   2. for every scheduled input width $r = r_0\gamma^{-j}\ge r_0/\gamma$, every shift $d$ and every eligible output $z = p+g$ ($g\in\Gamma$, $E_r(z)\in a_1(1\pm w_n)$),
--   $$\sum_{M\in d-g/2+\Gamma}\rho_{r/\sqrt2}(M)\,\mathbf 1[M\in W_r(z)] = V_{r/\sqrt2}(1\pm\eta_{\mathrm{mid}}),\qquad\eta_{\mathrm{mid}} = O(\epsilon_\Gamma)+e^{-\Omega(nw_n^2)},$$
--   where $W_r(z) = \{M : M\pm z/2\in S_r(a_0)\}$;
--   3. every eligible endpoint has weighted reference degree at most $D^+_j = \Upsilon_jB_j2^{b_{\deg}}$: $\sum_yK(x,y)\nu_{-p/2+d,r,\Upsilon_j}(y)\le D_j^+$ for $x\in(p/2+d+\Gamma)\cap S_r(a_0)$, and symmetrically for right endpoints.
--
--   These are the closure and degree estimates that make (45) a valid activation law and feed Corollary 4.6.
--
--   Differences from the source:
--   - reading: the schedule $w_n,h_n,\ell_n$ → either schedule of the paper (163) or (166); reason: Theorem 5.2 applies the lemma under both
--   - reading: $O$, $\Omega$, sufficiently large $n$ → explicit constants $C$, $c>0$ and $n_0$ fixed before $n$, $u$, $\Gamma$, $s$; reason: uniformity as stated
--   - encoding: $B_j$ at the input width $r$ → stated for every $r>0$; reason: $A_rR_-^2$ does not depend on $r$
--   - reading: every scheduled input $r\ge r_0/\gamma$, every shift → $r = r_0\gamma^{-j}$ for every $j\ge1$; $d = \tfrac12B\bar e$ for every $e\in(\mathbb Z/2)^n$; every offset $p$; reason: the scheduled widths and the half-grid shifts
--   - reading: weighted reference degree → $\sum_yK(x,y)\nu_{-p/2+d,r,\Upsilon}(y)$ with the reference (40) at any coefficient $\Upsilon>0$, for left and right endpoints; reason: the degree $D^\pm$ of Proposition 4.4 for (45)
-- source:
--   Gao–Han–Hu, Gaussian Difference Dynamics: Breaking the 2^{n/2} Barrier for the Shortest Vector Problem and Discrete Gaussian Sampling, arXiv:2611.04336 (held version, sha256 233bf8bb…0692), Lemma 5.1, p.28 (setting (39)–(45), pp.27–28)

import Mathlib
import Definitions.Def_SuperlatSVP_lat
import Definitions.Def_RegevLWE_GaussConv_Lattice
import Definitions.Def_GaussDiffSVP_AdmissibleBudget
import Definitions.Def_GaussDiffSVP_shell
import Definitions.Def_GaussDiffSVP_volFactor
import Definitions.Def_GaussDiffSVP_rateJ
import Definitions.Def_GaussDiffSVP_rateP
import Definitions.Def_GaussDiffSVP_coolPairWeight
import Definitions.Def_GaussDiffSVP_coolB
import Definitions.Def_GaussDiffSVP_halfGrid
import Definitions.Def_GaussDiffSVP_gaussRef

open SuperlatSVP
open scoped ENNReal

namespace GaussDiffSVP

/-- Lemma 5.1 (Gaussian closure and weighted degrees) (Gao–Han–Hu, *Gaussian Difference Dynamics*, arXiv:2611.04336 (held version, sha256 233bf8bb…0692), p.28), in the cooling setting (39)–(45)
(pp.27–28): `u ∈ (1/2, 31/50]`, `a₀ = 1/(1 + u)`, `a₁ = 4a₀ − 2`, `γ² = 2(1 − u)`; `Γ = Bℤⁿ` and `s`
with `ϵ_Γ = ρ_{1/s}(Γ*∖{0}) ≤ 2^{−h_n/3}`, `r₀ = √2 s`. Uniformly over (39) with `γ² ≤ 1 − w_n/4`,
for all sufficiently large `n`:

1. `B_j = 2^{−(J(a₀) + P(u₁))n + O(n w_n)}` (46), `u₁ = u`;
2. for every scheduled input width `r = r₀γ^{−j} ≥ r₀/γ`, shift `d` and eligible output `z = p + g`
   (`g ∈ Γ`, `E_r(z) ∈ a₁(1 ± w_n)`),
   `∑_{M ∈ d − g/2 + Γ} ρ_{r/√2}(M) 1[M ∈ W_r(z)] = V_{r/√2}(1 ± η_mid)`,
   `η_mid = O(ϵ_Γ) + e^{−Ω(n w_n²)}` (47), where `W_r(z) = {M : M ± z/2 ∈ S_r(a₀)}` (43);
3. every eligible endpoint has weighted reference degree at most `D_j^+ = Υ_j B_j 2^{b_deg}`
   (`b_deg = ⌈10ℓ_n⌉`): for `x ∈ (p/2 + d + Γ) ∩ S_r(a₀)`,
   `∑_y K(x, y) ν_{−p/2+d, r, Υ_j}(y) ≤ D_j^+`, and symmetrically for a right endpoint `y`, where
   `K(x, y) = 1[x, y ∈ S_r(a₀)] 1[E_r(x − y) ∈ a₁(1 ± w_n)] ω_r(x − y)` is the pair weight before the
   common factor `2^{−h_n}/D_j^+`.

**Formalization Note.** The schedule is either schedule of the paper (`AdmissibleBudget`). (46) is
stated for every `r > 0` (`B_j` does not depend on `r`), for every `n ≥ n₀`, with `O(n w_n)` as
`≤ C n w_n`. In (47) and the degree bound, `O` and `Ω` are explicit constants `C`, `c > 0` fixed before
`n`; the shift `d` ranges over the half-grid representatives `½Bē`; `p` and `Υ_j > 0` are arbitrary. -/
theorem lemma_5_1 :
    (∃ C : ℝ, ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n → ∀ β : Budget, AdmissibleBudget β →
      ∀ u : ℝ, 1 / 2 < u → u ≤ 31 / 50 → 2 * (1 - u) ≤ 1 - β.w n / 4 → ∀ r : ℝ, 0 < r →
        |Real.logb 2 (coolB n (β.w n) u r) + (rateJ (1 / (1 + u)) + rateP u) * n| ≤
          C * n * β.w n) ∧
    (∃ C c : ℝ, ∃ n₀ : ℕ, 0 < c ∧ ∀ n : ℕ, n₀ ≤ n → ∀ β : Budget, AdmissibleBudget β →
      ∀ u : ℝ, 1 / 2 < u → u ≤ 31 / 50 → 2 * (1 - u) ≤ 1 - β.w n / 4 →
      ∀ B : Matrix (Fin n) (Fin n) ℝ, B.det ≠ 0 → ∀ s : ℝ, 0 < s →
      let εΓ := rhoSet (1 / s) {y | y ∈ RegevLWE.GaussConv.dual (lat B) ∧ y ≠ 0}
      εΓ ≤ ENNReal.ofReal ((2 : ℝ) ^ (-(β.h n / 3))) →
      let ηmid := C * εΓ.toReal + Real.exp (-(c * n * β.w n ^ 2))
      ∀ j : ℕ, 1 ≤ j →
      let r := Real.sqrt 2 * s / Real.sqrt (2 * (1 - u)) ^ j
      ∀ p : E n, ∀ e : Fin n → ZMod 2,
        (∀ z : E n, z - p ∈ lat B → z ∈ shell r (β.w n) (4 / (1 + u) - 2) →
          ENNReal.ofReal ((1 - ηmid) * volFactor B (r / Real.sqrt 2)) ≤
            rhoSet (r / Real.sqrt 2)
              {M : E n | M - (halfGrid B e - (1 / 2 : ℝ) • (z - p)) ∈ lat B ∧
                M + (1 / 2 : ℝ) • z ∈ shell r (β.w n) (1 / (1 + u)) ∧
                M - (1 / 2 : ℝ) • z ∈ shell r (β.w n) (1 / (1 + u))} ∧
          rhoSet (r / Real.sqrt 2)
              {M : E n | M - (halfGrid B e - (1 / 2 : ℝ) • (z - p)) ∈ lat B ∧
                M + (1 / 2 : ℝ) • z ∈ shell r (β.w n) (1 / (1 + u)) ∧
                M - (1 / 2 : ℝ) • z ∈ shell r (β.w n) (1 / (1 + u))} ≤
            ENNReal.ofReal ((1 + ηmid) * volFactor B (r / Real.sqrt 2))) ∧
        (∀ Υ : ℝ, 0 < Υ →
          (∀ x : E n, x - ((1 / 2 : ℝ) • p + halfGrid B e) ∈ lat B →
            x ∈ shell r (β.w n) (1 / (1 + u)) →
            ∑' y : E n, coolPairWeight (β.w n) u r x y *
                gaussRef B r (β.w n) (1 / (1 + u)) Υ (-((1 / 2 : ℝ) • p) + halfGrid B e) y ≤
              ENNReal.ofReal (Υ * coolB n (β.w n) u r * (2 : ℝ) ^ ⌈10 * β.ell n⌉₊)) ∧
          (∀ y : E n, y - (-((1 / 2 : ℝ) • p) + halfGrid B e) ∈ lat B →
            y ∈ shell r (β.w n) (1 / (1 + u)) →
            ∑' x : E n, coolPairWeight (β.w n) u r x y *
                gaussRef B r (β.w n) (1 / (1 + u)) Υ ((1 / 2 : ℝ) • p + halfGrid B e) x ≤
              ENNReal.ofReal (Υ * coolB n (β.w n) u r * (2 : ℝ) ^ ⌈10 * β.ell n⌉₊)))) := by sorry

end GaussDiffSVP
