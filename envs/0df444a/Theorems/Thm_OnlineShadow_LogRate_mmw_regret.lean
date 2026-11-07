-- Prove2me | Theorems.Thm_OnlineShadow_LogRate_mmw_regret
-- name    : OnlineShadow.LogRate.mmw_regret
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T04:05:53.992197+00:00
-- url     : https://prove2.me/theorems/5975f3d3-54c1-47b6-8420-dcf0b6539bb3
-- title:
--   Regret bound of matrix multiplicative weights (proof of Lemma 4.4)
-- statement:
--   Let $d\ge1$ and $0<\eta\le1$. Let $A_0,\dots,A_{M-1}$ be effects on $\mathbb C^d$, $s_j\in\{-1,1\}$ signs and $L_j=s_jA_j$ the loss matrices, and let
--   $$\rho_j=\frac{\exp\big(-\eta\sum_{i<j}L_i\big)}{\mathrm{Tr}\exp\big(-\eta\sum_{i<j}L_i\big)}$$
--   be the matrix multiplicative weights iterates.
--
--   **Regret bound.** For every density matrix $\rho$ on $\mathbb C^d$,
--   $$\sum_{j<M}\mathrm{Tr}\big(L_j(\rho_j-\rho)\big)\le\eta\sum_{j<M}\big|\mathrm{Tr}(L_j\rho_j)\big|+\frac{\log d}\eta\le\eta M+\frac{\log d}\eta .$$
--
--   With $\eta=\varepsilon/8$ this is the display in the proof of Lemma 4.4, which bounds the number of flagged steps of Algorithm 1 by $O(\log d/\varepsilon^2)$.
--
--   **Formalization Note** $\log$ is the natural logarithm. The losses form a fixed sequence, which covers adaptively chosen losses. The platform's open item `QAlgorithms.Nannicini.mmwu_regret` implies this statement.
--
--   Differences from the source:
--   - reading: losses L = ±A⁽ᵗ⁾ with ‖L‖ ≤ 1, step size ε/8, dimension d, as used in the proof → L_j = s_j A_j with A_j effects, s_j = ±1, step size η with 0 < η ≤ 1, d ≥ 1; reason: the display is used for these losses, and log d needs d ≥ 1; η ≤ 1 covers every instance with a flag, since for ε > 4/3 both tests of Algorithm 1 are skipped (0 ≤ ν < 3ε/4 and ν > 1 − 3ε/4), so flags occur only at η = ε/8 ≤ 1/6, and at M = 0 the display is 0 ≤ log d/η (paper.md R10)
--   - encoding: step size ε/8 and 8 log d/ε → step size η and log d/η; reason: the substitution η = ε/8
--   - encoding: flags indexed j = 1, …, M → indices j = 0, …, M − 1; reason: relabelling
--   - encoding: Tr(·) of the product → the real part .trace.re; reason: every such trace is of a Hermitian operator or of a product of two Hermitian operators, so it is real and the real part is its value
-- source:
--   Chen, O'Donnell, Pelecanos, Wright, Online Shadow Tomography Matching the Classical Bounds, STOC 2027 submission (manuscript of November 2, 2026, sha256 90993723…dc3a9), unnumbered display in the proof of Lemma 4.4, p. 12 (cited from [Kal07, Corollary 3])

import Mathlib
import Definitions.Def_WildeQIT_IsDensityOperator
import Definitions.Def_ShadowTomography_UpperBound_IsEffect
import Definitions.Def_OnlineShadow_LogRate_gibbs

open scoped ComplexOrder

namespace OnlineShadow.LogRate

/-- **Matrix multiplicative weights regret bound** (Chen, O'Donnell, Pelecanos, Wright, *Online Shadow Tomography Matching the Classical Bounds*, STOC 2027 submission (manuscript of November 2, 2026, sha256 90993723…dc3a9), unnumbered display in the proof of Lemma 4.4, p.12,
cited from [Kal07, Corollary 3]). Let `d ≥ 1`, `0 < η ≤ 1`, let `A₀, …, A_{M−1}` be effects on `ℂ^d`
and `sⱼ ∈ {−1, 1}` signs, `Lⱼ = sⱼAⱼ`, and `ρⱼ = e^{−η∑_{i<j} Lᵢ} / Tr e^{−η∑_{i<j} Lᵢ}`. Then for every
density matrix `ρ`, `∑_{j<M} Tr(Lⱼ(ρⱼ − ρ)) ≤ η ∑_{j<M} |Tr(Lⱼρⱼ)| + log d / η ≤ ηM + log d / η`.

**Formalization Note** (paper.md R10) The display is stated for the losses of the protocol, `L = ±A`
with `0 ⪯ A ⪯ 1`, and step size `η = ε/8` (so `8 log d/ε = log d/η`), with `0 < η ≤ 1` as in the cited
result. Both inequalities of the display are stated (the second is `≤ εM/8 + 8 log d/ε` at `η = ε/8`). The losses are a fixed sequence, which covers adaptively chosen ones. `log` is
the natural logarithm. Related Open platform item: `QAlgorithms.Nannicini.mmwu_regret`, which implies
this one. -/
theorem mmw_regret {d : ℕ} (hd : 1 ≤ d) (η : ℝ) (hη : 0 < η) (hη1 : η ≤ 1) (M : ℕ)
    (A : ℕ → Matrix (Fin d) (Fin d) ℂ) (hA : ∀ j < M, ShadowTomography.UpperBound.IsEffect (A j))
    (s : ℕ → ℝ) (hs : ∀ j < M, s j = 1 ∨ s j = -1)
    (ρ : Matrix (Fin d) (Fin d) ℂ) (hρ : WildeQIT.IsDensityOperator ρ) :
    let Lm : ℕ → Matrix (Fin d) (Fin d) ℂ := fun j => ((s j : ℝ) : ℂ) • A j
    let ρj : ℕ → Matrix (Fin d) (Fin d) ℂ :=
      fun j => gibbs (((η : ℝ) : ℂ) • ∑ i ∈ Finset.range j, Lm i)
    ∑ j ∈ Finset.range M, (Lm j * (ρj j - ρ)).trace.re ≤
        η * ∑ j ∈ Finset.range M, |(Lm j * ρj j).trace.re| + Real.log d / η ∧
      η * ∑ j ∈ Finset.range M, |(Lm j * ρj j).trace.re| + Real.log d / η ≤
        η * M + Real.log d / η := by sorry

end OnlineShadow.LogRate
