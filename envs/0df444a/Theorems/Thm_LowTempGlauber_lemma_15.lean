-- Prove2me | Theorems.Thm_LowTempGlauber_lemma_15
-- name    : LowTempGlauber.lemma_15
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T12:27:05.028212+00:00
-- url     : https://prove2.me/theorems/5fd9d83b-0842-410b-92a1-46463d7fdf7a
-- title:
--   Lemma 15 — the annealing product $Z_{t_0}\prod_{i<m}e^{hH(X_i)}$ is an upper-$\delta$-tailed estimator for $Z_{t_m}$
-- statement:
--   Let $\Omega$ be a finite nonempty set with weights $w>0$ and a Hamiltonian $H:\Omega\to[-H_{\max},H_{\max}]$, and let $Z_t,\mu_t$ be as in §3.3. Let $\delta\in(0,1/4)$ and let $h$ satisfy $1/h\ge10H_{\max}\log(4/\delta)$. For $t_0\in\mathbb R$ and an integer $m\ge1$ let $t_i=t_0+ih$. If $X_0,\dots,X_{m-1}$ are independent with $X_i\sim\mu_{t_i}$, then
--   $$W=Z_{t_0}\prod_{i=0}^{m-1}e^{hH(X_i)}$$
--   is an upper-$\delta$-tailed estimator for $Z_{t_m}$.
--
--   Applied to $H=-M$ along the cooling schedule, this gives the estimators of the phase partition functions in the proof of Theorem 1, part 2.
--
--   **Formalization Note** The law of $W$ is the finite mixture of point masses at $Z_{t_0}\prod_ie^{hH(x_i)}$ over the sequences $(x_i)$, with weights $\prod_i\mu_{t_i}(x_i)$. $\log$ is the natural logarithm.
--
--   Differences from the source:
--   - encoding: a finite space Ω → a finite nonempty type Ω; reason: μ_t is a probability distribution only on a nonempty space
-- source:
--   Galanis–Štefankovič, Low-Temperature Sampling via Equilibrium Disagreements, STOC 2027 submission (manuscript sha256 c41a38ff…7533d), Lemma 15, p.16; setup §3.3, p.15

import Mathlib
import Definitions.Def_LowTempGlauber_Gibbs

namespace LowTempGlauber

open MeasureTheory

/-- Galanis–Štefankovič, *Low-Temperature Sampling via Equilibrium Disagreements*, STOC 2027
submission (manuscript sha256 c41a38ff…), Lemma 15, p.16, in the setting of §3.3, p.15.

Let `Ω` be a finite space with weights `w > 0` and Hamiltonian `H : Ω → [−H_max, H_max]`. Let
`δ ∈ (0, 1/4)` and `h` satisfy `1/h ≥ 10 H_max log(4/δ)`. For `t₀ ∈ ℝ` and an integer `m ≥ 1` let
`t_i = t₀ + ih`. For independent `X_i ∼ μ_{t_i}`, `i = 0, …, m − 1`, the random variable
`W = Z_{t₀} ∏_{i=0}^{m−1} e^{hH(X_i)}` is an upper-`δ`-tailed estimator for `Z_{t_m}`.

**Formalization Note.** The law of `W` is the finite mixture of Dirac masses over the sequences
`x : Fin m → Ω`, with weight `∏ μ_{t_i}(x_i)`. `Ω` is nonempty, so that `μ_t` is a distribution.
`log` is natural. -/
theorem lemma_15 {Ω : Type*} [Fintype Ω] [Nonempty Ω] (w H : Ω → ℝ) (hw : ∀ x, 0 < w x)
    (Hmax : ℝ) (hH : ∀ x, |H x| ≤ Hmax) (δ h : ℝ) (hδ0 : 0 < δ) (hδ1 : δ < 1 / 4)
    (hh : 10 * Hmax * Real.log (4 / δ) ≤ 1 / h) (t₀ : ℝ) (m : ℕ) (hm : 1 ≤ m) :
    IsUpperTailed δ (Zt w H (t₀ + m * h))
      (∑ x : Fin m → Ω, ENNReal.ofReal (∏ i : Fin m, muT w H (t₀ + (i : ℕ) * h) (x i)) •
        Measure.dirac (Zt w H t₀ * ∏ i : Fin m, Real.exp (h * H (x i)))) := by sorry

end LowTempGlauber
