-- Prove2me | Theorems.Thm_IllCondRegMem_lemma_12
-- name    : IllCondRegMem.lemma_12
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T09:56:09.425195+00:00
-- url     : https://prove2.me/theorems/dfb7bdb2-455b-46bd-988e-78831628d8f2
-- title:
--   Lemma 12 — properties of the smoothing kernel: envelope, $\|\phi\|_1\le C\delta R$, $\|\phi'\|_1\le C(\delta R^2+R)$, $0\le\hat\phi\le1$
-- statement:
--   Let $\phi$ be the kernel of eq. (6) with parameters $R>0$ and $r=r_0=\delta/2$, $\delta>0$. There is an absolute constant $C>0$ such that, for all such $R,\delta$, $\phi$ is integrable and differentiable and
--
--   1. $|\phi(t)|\le CR\,e^{-t^2/(2r_0^2)}$ for all $t$;
--   2. $\|\phi\|_1\le C\delta R$;
--   3. $\|\phi'\|_1\le C(\delta R^2+R)$;
--   4. $\hat\phi$ is real-valued with $0\le\hat\phi\le1$;
--   5. for $|x|\le R$,
--   $$
--   |1-\hat\phi(x)|\le 2e^{-r^2R^2/2}.
--   $$
--
--   These bounds control the error of smoothing a density along a line (Lemma 13) and the translation stability of the averaged kernel (Lemma 14).
--
--   **Formalization Note** $\hat\phi(\xi)=\int\phi(t)e^{i\xi t}\,dt$; $\|\cdot\|_1$ is the Lebesgue $L^1$ norm.
--
--   Differences from the source:
--   - reading: r in (6), r₀ in (7), δ undefined in the lemma → r = r₀ = δ/2 for all R, δ > 0, one absolute C; reason: Appendix A (p.39) fixes r₀ = δ/2 and uses ϕ with r₀
--   - encoding: 0 ≤ ϕ̂ ≤ 1 for the non-unitary transform → phiHat has zero imaginary part and real part in [0,1]; reason: ϕ̂ is complex-valued in Lean
--   - encoding: ‖ϕ‖₁, ‖ϕ′‖₁, ϕ̂ for the kernel → lower L¹ integrals, with integrability and differentiability of ϕ added to the conclusion; reason: makes the integrals and the derivative genuine; true for the kernel
-- source:
--   M. Blanchard, D. Hansen, A. Jayant, V. Sharan, Polynomial Memory-Sample Separations in Non-i.i.d. Ill-Conditioned Regression, STOC 2027 submission (held version, sha256 6369d09f…), Lemma 12, p.11 (PDF p.12); parameters from App. A, p.39 (PDF p.40)

import Mathlib
import Definitions.Def_IllCondRegMem_phi

open MeasureTheory

namespace IllCondRegMem

/-- **Lemma 12 (Properties of the smoothing function).**
Blanchard, Hansen, Jayant, Sharan, *Polynomial Memory-Sample Separations in Non-i.i.d.
Ill-Conditioned Regression*, STOC 2027 submission (held version, sha256 6369d09f…), Lemma 12,
p.11: "The function Equation 6 satisfies the following properties: |ϕ(t)| ≤ CRe^{−t²/(2r₀²)} (7),
‖ϕ‖₁ ≤ CδR (8), ‖ϕ′‖₁ ≤ C(δR² + R). (9) Moreover, 0 ≤ ϕ̂ ≤ 1 and |1 − ϕ̂(x)| ≤ 2e^{−r²R²/2},
|x| ≤ R."

**Formalization Note.** The parameters are those fixed in Appendix A (p.39): `r = r₀ = δ/2`
with `R, δ > 0` arbitrary, and one absolute constant `C`. `ϕ̂` is the paper's non-unitary
transform `∫ ϕ(t)e^{iξt} dt` (`phiHat`); "0 ≤ ϕ̂ ≤ 1" is stated as: `ϕ̂(ξ)` is real (zero
imaginary part) with real part in `[0, 1]`. `‖·‖₁` is the Lebesgue `L¹` norm (a lower integral,
so it is finite only for integrable functions). Integrability and differentiability of `ϕ` are
stated as part of the conclusion, so `ϕ̂` and `ϕ′` are genuine. -/
theorem lemma_12 :
    ∃ C : ℝ, 0 < C ∧ ∀ R δ : ℝ, 0 < R → 0 < δ →
      Integrable (phi R (δ / 2)) ∧ Differentiable ℝ (phi R (δ / 2)) ∧
      (∀ t : ℝ, |phi R (δ / 2) t| ≤ C * R * Real.exp (-t ^ 2 / (2 * (δ / 2) ^ 2))) ∧
      (∫⁻ t : ℝ, ENNReal.ofReal |phi R (δ / 2) t|) ≤ ENNReal.ofReal (C * δ * R) ∧
      (∫⁻ t : ℝ, ENNReal.ofReal |deriv (phi R (δ / 2)) t|) ≤
        ENNReal.ofReal (C * (δ * R ^ 2 + R)) ∧
      (∀ ξ : ℝ, (phiHat R (δ / 2) ξ).im = 0 ∧ 0 ≤ (phiHat R (δ / 2) ξ).re ∧
        (phiHat R (δ / 2) ξ).re ≤ 1) ∧
      (∀ x : ℝ, |x| ≤ R →
        ‖1 - phiHat R (δ / 2) x‖ ≤ 2 * Real.exp (-(δ / 2) ^ 2 * R ^ 2 / 2)) := by sorry

end IllCondRegMem
