-- Prove2me | Theorems.Thm_GEGIAMP_Relative_lemma_8_13
-- name    : GEGIAMP.Relative.lemma_8_13
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T15:54:59.116484+00:00
-- url     : https://prove2.me/theorems/db8e0df5-1ced-405b-8ad1-a4a00b5149f7
-- title:
--   Lemma 8.13 — energy before clipping
-- statement:
--   Fix $\omega$ satisfying (7.116) and $t_{\rm dev}\ge1$. Suppose $d\le N$, $N\ge d+t_{\rm dev}$, (8.39) $N\ge KR\{t_{\rm dev}+\log(Kd)\}$ holds and $r_N$, $r_N^2=\nu^2+\overline V(d+t_{\rm dev})/N$ (8.40), is sufficiently small. With failure at most $Ke^{-t_{\rm dev}}$, $|H_N(f)/N-(\mathcal E-c_1)|\le K\{\nu+\sqrt{\overline Vt_{\rm dev}/N}+\overline V(d+t_{\rm dev})/N\}$ (8.67) and $\|f\|/\sqrt N\le5/4$ (8.68).
--
--   Differences from the source:
--   - reading: Φ_γ is the solution of the Parisi PDE (2.3); m = Φₓ, a = Φₓₓ → Φ is `value` of the published SKFullSupport bundle (the stochastic-control formula (5.2)); m = `gradient`, a = `curvature` (Lean `deriv`), aₓ, aₓₓ further `deriv`s; reason: the paper identifies Φ with (5.2) on p. 15 (citing [AC17, Cor. 2]); Proposition 5.1 gives the spatial derivatives below time one
--   - encoding: "we fix a minimizing γ" (p. 7) and Assumption 2.1 for the Parisi diffusion (2.5) → hypothesis `Standing W γ`: IsMinimizer W γ and E[m(t,X_t)²] = t (0 ≤ t < 1) for every X with IsDiffusion W γ X (the integral form of (2.5)); reason: standing hypotheses of §§3, 7–9, written as binders
--   - reading: "r_N is sufficiently small"; the universal K of (8.39) and of the conclusion → ∃ C, c > 0 with r_N ≤ c; the same C in (8.39) and in (8.67) and the failure bound; reason: "sufficiently small" is a threshold constant; one universal constant serves all displays
--   - reading: V of (8.27) with "a sufficiently large universal K_x" so that ω_j ≥ 1/2 and (7.10) bound the conditional variance → every K_x > 0 with 4a(t,x)² ≤ K_x Λ(t) on [0,1) × ℝ; reason: this is the property K_x is chosen for (a²/ω² ≤ 4a² when ω ≥ 1/2); any such K_x works
--   - reading: ν, R and the grid of §6 at internal accuracy ε → ν = c_ν ε/log(4d) for any c_ν > 0, R = K_R Λ(T) with K_R as in (6.5), any positive κ, 0 < ε ≤ 1, real t_dev ≥ 1; reason: the section’s standing parameters
--   - encoding: "with failure at most Ke^{−t_dev}" → the outer measure of the failure set under GOE(N) ⊗ law(J) ⊗ side variables is ≤ C e^{−t_dev}; reason: no measurability side condition; f is the vector of the construction with the final query appended (same f by Proposition 8.4)
--   - encoding: c_1, the first group’s correlation (8.6) → `cGroup … 0` (groups 0-based); reason: Lean convention
-- source:
--   Herman, Chakrabarti, Kim, Ozgul (2026), A Fully Polynomial Approximation Algorithm for the Sherrington–Kirkpatrick Model, arXiv:2611.05446v1 (version not printed; held file SHA-256 ea6508afbf5e8771a5353c9c9ce9df52a08608793fb812fc9ba947719fd5658e), Lemma 8.13, p. 55

import Mathlib
import Definitions.Def_GEGIAMP_Relative_Algorithm

open MeasureTheory ProbabilityTheory OAI.ZeroTemperatureSK
open scoped ENNReal NNReal Topology

namespace GEGIAMP.Relative

/-- **Lemma 8.13** (energy before clipping; Herman, Chakrabarti, Kim, Ozgul (2026), arXiv:2611.05446v1, SHA-256 ea6508af…5658e, p. 55). Fix `ω` satisfying (7.116)
(with `ν` from (6.18)) and `t_dev ≥ 1`. Suppose `d ≤ N`, `N ≥ d + t_dev`, (8.39)
`N ≥ K R {t_dev + log(K d)}` holds and `r_N`, `r_N² = ν² + V̄(d + t_dev)/N` (8.40), is
sufficiently small. With failure at most `K e^{−t_dev}`,
`|H_N(f)/N − (E − c_1)| ≤ K{ν + √(V̄ t_dev/N) + V̄(d + t_dev)/N}` (8.67) and
`‖f‖/√N ≤ 5/4` (8.68). Here `f` is the vector (6.15) of the construction with factors `ω`,
`E` is (6.17), `c_1` is (8.6) for the first group, `V̄ = 1 + V` with `V` from (8.27). -/
theorem lemma_8_13 {Ω : Type*} [MeasurableSpace Ω] (W : BrownianSystem Ω)
    (γ : OrderParameter) (hγ : Standing W γ) (κ : AlgConsts) (hκ : κ.Pos)
    (hKR : KRValid W γ κ) (cν : ℝ) (hcν : 0 < cν) (Kx : ℝ) (hKx0 : 0 < Kx)
    (hKx : ∀ t x : ℝ, 0 ≤ t → t < 1 → 4 * aF W γ t x ^ 2 ≤ Kx * Lam t) :
    ∃ C c : ℝ, 0 < C ∧ 0 < c ∧
      ∀ (ε : ℝ), 0 < ε → ε ≤ 1 →
      let P := params κ ε
      let Γc := Gq (gam γ) κ ε
      let ρ := rhoOf (mF W γ) (aF W γ) P.h Γc P.K
      let ν := nuOf cν ε P.d
      let Vb := Vbar Kx P
      ∀ (ω : ℕ → ℝ), Cond7116 ω ρ ν P.K →
      ∀ (tdev : ℝ) (N : ℕ), 1 ≤ tdev → P.d ≤ N → (P.d : ℝ) + tdev ≤ N →
        C * Rq κ ε * (tdev + Real.log (C * P.d)) ≤ N →
        Real.sqrt (ν ^ 2 + Vb * (P.d + tdev) / N) ≤ c →
        matLaw N P {x | ¬ (
          |H x.1 (fvec (mF W γ) (aF W γ) P Γc ω x.1 (Jfun x.2.1) (sideFun x.2.2)) / N -
              (corrE (mF W γ) (aF W γ) P.h Γc P.K - cGroup (mF W γ) (aF W γ) P Γc 0)| ≤
            C * (ν + Real.sqrt (Vb * tdev / N) + Vb * (P.d + tdev) / N) ∧
          vnorm (fvec (mF W γ) (aF W γ) P Γc ω x.1 (Jfun x.2.1) (sideFun x.2.2)) /
              Real.sqrt N ≤ 5 / 4)} ≤
          ENNReal.ofReal (C * Real.exp (-tdev)) := by sorry

end GEGIAMP.Relative
