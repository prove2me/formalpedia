-- Prove2me | Theorems.Thm_GaussDiffSVP_proposition_3_6
-- name    : GaussDiffSVP.proposition_3_6
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T22:02:43.526873+00:00
-- url     : https://prove2.me/theorems/99f68780-0282-4539-8f9e-b578991a58df
-- title:
--   Proposition 3.6 — the random superlattice $\Gamma = L+\mathbb ZBv/p$: index, smoothing, flatness, energy
-- statement:
--   Let $L = B\mathbb Z^n$ be a full-rank rational lattice and $Q$ a squared scale with $Q\le\lambda_1(L)^2<(1+1/n)Q$. Choose a rational approximation to
--   $$s^2 = \frac{2\pi A_G}{n}Q\,(1+O(1/n)),\qquad A_G = \frac{e}{2^{2\kappa_{\mathrm{pack}}}},\ \kappa_{\mathrm{pack}} = \tfrac{401}{1000}.$$
--   There is a prime $p = \Theta(2^{h_n}\det L/s^n)$ of polynomial bit length such that, for $K = p^{-1}L$ and a uniformly random line $U\subset K/L\cong\mathbb F_p^n$ with inverse image $\Gamma$ (equivalently $\Gamma = L+\mathbb ZBv/p$ for a uniform nonzero $v\in\mathbb F_p^n$):
--
--   1. $[\Gamma:L] = p$ and $s^n/\det\Gamma = 2^{h_n+O(1)}$;
--   2. $\Pr\big[\rho_{1/s}(\Gamma^*\setminus\{0\})>2^{-h_n/3}\big]\le 2^{-2h_n/3+O(\log n)}$;
--   3. for every shortest vector $v$ of $L$, $E_{r_0}(v) = c+O(1/n)$ with $r_0 = \sqrt2 s$ and $c = 2^{2\kappa_{\mathrm{pack}}-1}/e$, and on the good event $\rho_{1/s}(\Gamma^*\setminus\{0\})\le2^{-h_n/3}$, $V_{r_0} = 2^{n/2+h_n+O(1)}$;
--   4. for every permitted scale and prime and every fixed $a_*>0$, uniformly over shifts $b$ and $t\ge a_*s$,
--   $$\rho_t(b+K) = \frac{t^n}{\det K}\big(1+O(2^{-\Omega(h_n)})\big).$$
--
--   The random superlattice supplies smoothing at the scale of a shortest vector, which is what lets the SVP algorithm run Gaussian dynamics on $\Gamma$ instead of $L$.
--
--   Differences from the source:
--   - reading: rational approximation $s^2 = (2\pi A_G/n)Q(1+O(1/n))$ → for every fixed $C_s>0$, uniformly over $s>0$ with $s^2\in\mathbb Q$ and $|s^2-2\pi A_GQ/n|\le (C_s/n)(2\pi A_GQ/n)$; reason: the $O(1/n)$ constant is fixed before $n$
--   - reading: $\Theta$, $O$, $\Omega$ in $n$ → explicit constants fixed before $n$, estimates for $n\ge n_0$; reason: standard asymptotic reading
--   - reading: polynomial bit length → $\log_2p\le C(\ell+1)^k$ in the input length $\ell$ of $B$; reason: polynomial in the input length
--   - reading: for every permitted scale and prime (18) → every $Q,s$ as above and every prime $p$ in the window $[c_1X,c_2X]$, $X = 2^{h_n}\det L/s^n$, with the window constants of clause 1; reason: the permitted primes are those of size $\Theta(X)$
--   - encoding: uniform line $U\subset K/L$ → uniform nonzero generator $v$ of $\Gamma = L+\mathbb ZBv/p$ (`SuperlatSVP.indexExt`); probabilities are counts over $p^n-1$; reason: each line has $p-1$ generators; the page states this representation
--   - encoding: $\det\Gamma$, $\det K$, $[\Gamma:L]$ → $\det L/p$, $\det L/p^n$, `AddSubgroup.relIndex`; reason: $\det\Gamma = \det L/[\Gamma:L]$
--   - encoding: $E_{r_0}(v) = c_n$ stated on the good event → stated for every shortest vector; reason: $E_{r_0}(v)$ does not depend on $\Gamma$
--   - encoding: $L$ full-rank rational, $h_n$ → $B\in\mathbb Q^{n\times n}$ with $\det B\ne0$; $h_n$ of the default schedule (163); reason: the SVP setting
-- source:
--   Gao–Han–Hu, Gaussian Difference Dynamics: Breaking the 2^{n/2} Barrier for the Shortest Vector Problem and Discrete Gaussian Sampling, arXiv:2611.04336 (held version, sha256 233bf8bb…0692), Proposition 3.6, p.22; App. B.9.1, p.79

import Mathlib
import Definitions.Def_SuperlatSVP_SolvesSVPWithin
import Definitions.Def_SuperlatSVP_indexExt
import Definitions.Def_RegevLWE_GaussConv_Lattice
import Definitions.Def_GaussDiffSVP_svpBudget
import Definitions.Def_GaussDiffSVP_energy

open SuperlatSVP
open scoped ENNReal

namespace GaussDiffSVP

/-- Proposition 3.6 (Gao–Han–Hu, *Gaussian Difference Dynamics*, arXiv:2611.04336 (held version, sha256 233bf8bb…0692), p.22). Let `L = Bℤⁿ` be a full-rank rational lattice and let the squared
scale `Q` satisfy `Q ≤ λ₁(L)² < (1 + 1/n)Q`. Choose a rational approximation to
`s² = (2πA_G/n) Q (1 + O(1/n))`, `A_G = e/2^{2κ_pack}`, `κ_pack = 401/1000`. There is a prime
`p = Θ(2^{h_n} det L / sⁿ)` of polynomial bit length such that, for `K = p⁻¹L` and a uniformly
random line `Γ = L + ℤBv/p` (`v` uniform in `𝔽_pⁿ∖{0}`):

1. `[Γ : L] = p` and `sⁿ / det Γ = 2^{h_n + O(1)}`;
2. `P[ρ_{1/s}(Γ*∖{0}) > 2^{−h_n/3}] ≤ 2^{−2h_n/3 + O(log n)}` (17);
3. (19): for any shortest vector `v` of `L`, `E_{r₀}(v) = c + O(1/n)` with `r₀ = √2 s` and
   `c = 2^{2κ_pack − 1}/e`; and on the good event `ρ_{1/s}(Γ*∖{0}) ≤ 2^{−h_n/3}`,
   `V_{r₀} = r₀ⁿ/det Γ = 2^{n/2 + h_n + O(1)}`;
4. (18): for every permitted scale and prime (every prime in the window `Θ(2^{h_n} det L/sⁿ)`), for
   every fixed `a_* > 0`, uniformly over shifts `b` and `t ≥ a_* s`,
   `ρ_t(b + K) = (tⁿ/det K)(1 + O(2^{−Ω(h_n)}))`.

**Formalization Note.** `h_n` is the default schedule (163). "Rational approximation … (1 + O(1/n))"
reads: for every fixed `C_s > 0`, uniformly over `s > 0` with `s²` rational and
`|s² − 2πA_G Q/n| ≤ (C_s/n)(2πA_G Q/n)`. Asymptotic notation is quantified explicitly: `Θ`, `O`, `Ω`
constants are fixed before `n`, and the estimates hold for `n ≥ n₀`. "Polynomial bit length" is
`log₂ p ≤ C(ℓ + 1)^k` in the input length `ℓ = inputBits B`. The uniform line is encoded by its
generator `v` (uniform nonzero; each line has `p − 1` generators, so the laws agree), via the
published `SuperlatSVP.indexExt`; probabilities over `v` are counts divided by `pⁿ − 1`.
`[Γ : L]` is `AddSubgroup.relIndex`; `det Γ` is written `det L / p`, its value when `[Γ : L] = p`;
`det K = det L / pⁿ`. -/
theorem proposition_3_6 :
    ∀ Cs : ℝ, 0 < Cs → ∃ c₁ c₂ C : ℝ, ∃ k n₀ : ℕ, 0 < c₁ ∧ c₁ ≤ c₂ ∧
      (∀ n : ℕ, n₀ ≤ n → ∀ B : Matrix (Fin n) (Fin n) ℚ, B.det ≠ 0 → ∀ Q s : ℝ, 0 < Q →
        Q ≤ lam1 (lat (B.map (↑))) ^ 2 → lam1 (lat (B.map (↑))) ^ 2 < (1 + 1 / (n : ℝ)) * Q →
        0 < s → (∃ q : ℚ, s ^ 2 = q) →
        |s ^ 2 - 2 * Real.pi * (Real.exp 1 / (2 : ℝ) ^ (2 * (401 / 1000 : ℝ))) * Q / n| ≤
          Cs / n * (2 * Real.pi * (Real.exp 1 / (2 : ℝ) ^ (2 * (401 / 1000 : ℝ))) * Q / n) →
        ∃ p : ℕ, p.Prime ∧
          c₁ * ((2 : ℝ) ^ svpBudget.h n * |(B.map ((↑) : ℚ → ℝ)).det| / s ^ n) ≤ p ∧
          (p : ℝ) ≤ c₂ * ((2 : ℝ) ^ svpBudget.h n * |(B.map ((↑) : ℚ → ℝ)).det| / s ^ n) ∧
          Real.logb 2 p ≤ C * ((inputBits B : ℝ) + 1) ^ k ∧
          (∀ v : Fin n → ZMod p, v ≠ 0 →
            (lat (B.map (↑))).toAddSubgroup.relIndex
              (indexExt (B.map (↑)) p v).toAddSubgroup = p) ∧
          (2 : ℝ) ^ (svpBudget.h n - C) ≤ s ^ n / (|(B.map ((↑) : ℚ → ℝ)).det| / p) ∧
          s ^ n / (|(B.map ((↑) : ℚ → ℝ)).det| / p) ≤ (2 : ℝ) ^ (svpBudget.h n + C) ∧
          ({v : Fin n → ZMod p | v ≠ 0 ∧
              ENNReal.ofReal ((2 : ℝ) ^ (-(svpBudget.h n / 3))) <
                rhoSet (1 / s) {y | y ∈ RegevLWE.GaussConv.dual (indexExt (B.map (↑)) p v) ∧
                  y ≠ 0}}.ncard : ℝ) / ((p : ℝ) ^ n - 1) ≤
            (2 : ℝ) ^ (-(2 * svpBudget.h n / 3) + C * Real.logb 2 (n + 2)) ∧
          (∀ v : E n, v ∈ lat (B.map (↑)) → v ≠ 0 → ‖v‖ = lam1 (lat (B.map (↑))) →
            |energy (Real.sqrt 2 * s) v -
                (2 : ℝ) ^ (2 * (401 / 1000 : ℝ) - 1) / Real.exp 1| ≤ C / n) ∧
          (∀ v : Fin n → ZMod p, v ≠ 0 →
            rhoSet (1 / s) {y | y ∈ RegevLWE.GaussConv.dual (indexExt (B.map (↑)) p v) ∧
                y ≠ 0} ≤ ENNReal.ofReal ((2 : ℝ) ^ (-(svpBudget.h n / 3))) →
              (2 : ℝ) ^ ((n : ℝ) / 2 + svpBudget.h n - C) ≤
                (Real.sqrt 2 * s) ^ n / (|(B.map ((↑) : ℚ → ℝ)).det| / p) ∧
              (Real.sqrt 2 * s) ^ n / (|(B.map ((↑) : ℚ → ℝ)).det| / p) ≤
                (2 : ℝ) ^ ((n : ℝ) / 2 + svpBudget.h n + C))) ∧
      (∀ aStar : ℝ, 0 < aStar → ∃ C' c' : ℝ, ∃ n₁ : ℕ, 0 < c' ∧
        ∀ n : ℕ, n₁ ≤ n → ∀ B : Matrix (Fin n) (Fin n) ℚ, B.det ≠ 0 → ∀ Q s : ℝ, 0 < Q →
          Q ≤ lam1 (lat (B.map (↑))) ^ 2 → lam1 (lat (B.map (↑))) ^ 2 < (1 + 1 / (n : ℝ)) * Q →
          0 < s → (∃ q : ℚ, s ^ 2 = q) →
          |s ^ 2 - 2 * Real.pi * (Real.exp 1 / (2 : ℝ) ^ (2 * (401 / 1000 : ℝ))) * Q / n| ≤
            Cs / n * (2 * Real.pi * (Real.exp 1 / (2 : ℝ) ^ (2 * (401 / 1000 : ℝ))) * Q / n) →
          ∀ p : ℕ, p.Prime →
            c₁ * ((2 : ℝ) ^ svpBudget.h n * |(B.map ((↑) : ℚ → ℝ)).det| / s ^ n) ≤ p →
            (p : ℝ) ≤ c₂ * ((2 : ℝ) ^ svpBudget.h n * |(B.map ((↑) : ℚ → ℝ)).det| / s ^ n) →
            ∀ b : E n, ∀ t : ℝ, aStar * s ≤ t →
              ENNReal.ofReal (t ^ n / (|(B.map ((↑) : ℚ → ℝ)).det| / (p : ℝ) ^ n) *
                  (1 - C' * (2 : ℝ) ^ (-(c' * svpBudget.h n)))) ≤
                rhoSet t {x | x - b ∈ lat ((p : ℝ)⁻¹ • B.map (↑))} ∧
              rhoSet t {x | x - b ∈ lat ((p : ℝ)⁻¹ • B.map (↑))} ≤
                ENNReal.ofReal (t ^ n / (|(B.map ((↑) : ℚ → ℝ)).det| / (p : ℝ) ^ n) *
                  (1 + C' * (2 : ℝ) ^ (-(c' * svpBudget.h n))))) := by sorry

end GaussDiffSVP
