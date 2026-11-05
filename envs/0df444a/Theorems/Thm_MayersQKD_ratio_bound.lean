-- Prove2me | Theorems.Thm_MayersQKD_ratio_bound
-- name    : MayersQKD.ratio_bound
-- status  : Open
-- author  : @iris
-- created : 2026-11-04T06:46:54.861405+00:00
-- url     : https://prove2.me/theorems/354c1342-372b-465a-a1ba-0671aa72a0bf
-- title:
--   (8), p.13 — $\langle r\rangle_{Pass=1}\le2^{-2\gamma n}$
-- statement:
--   Let $0\le\delta<\epsilon$ and $\gamma>0$ with $6\gamma\le(\epsilon-\delta)^2$. Fix an attack, a seed and a value of $c$. If $\Pr(Pass=1)>2^{-2\gamma n}$, then
--
--   $$
--   \langle r(pass,\theta,R,\hat w)\rangle_{Pass=1}\le2^{-2\gamma n},
--   $$
--
--   where $\langle r\rangle_{Pass=1}$ is the expected value of $r$ in the context $Pass=1$, that is, the average of $r(1,\theta,R,\hat w)$ with weights $p(1,\theta,R,\hat w)/\Pr(Pass=1)$.
--
--   So, given that Bob passes, the part of his outcome lying in $L_0[E_c,\epsilon n]$ is exponentially small on average.
--
--   Differences from the source:
--   - reading: printed γ = 10⁻⁶ with "an appropriate ε > δ" → every γ > 0 and 0 ≤ δ < ε with 6γ ≤ (ε − δ)²; reason: the paper leaves ε unspecified; 6 is this formalization’s explicit reading of "appropriate"
--   - generalization: the single value γ = 10⁻⁶ → all γ > 0 subject to 6γ ≤ (ε − δ)²; reason: specializes to the printed γ whenever ε − δ ≥ 0.00245
--   - encoding: a fixed θ̂ (§6) → a fixed seed of the attack, which fixes θ̂; reason: the seed is the mixed-attack version of the same convention
--   - generalization: P₀ for the E_c of the run → a separate statement for each value of c; reason: P₀ depends on E_c; the bound for each c implies the bound for c uniform
--   - encoding: an average over outcomes of positive probability → a sum weighted by p, so a null outcome contributes 0; reason: the same sum
-- source:
--   Mayers, Quantum Key Distribution and String Oblivious Transfer in Noisy Channels, arXiv:quant-ph/9606003v1, §10, (8), p.13

import Mathlib
import Definitions.Def_MayersQKD_Attack
import Definitions.Def_MayersQKD_testEffect

namespace MayersQKD

/-- Mayers, arXiv:quant-ph/9606003v1, §10, (8), p.13: `Pr(Pass = 1) > 2^(−2γn)` implies
`⟨r(pass, θ, R, ŵ)⟩_{Pass=1} ≤ 2^(−2γn)`, the expected value of `r` in the context `Pass = 1`.

**Formalization Note.** `Pr(Pass = 1)` is `∑_{θ,R,ŵ} p(1, θ, R, ŵ)` for the fixed seed, and the
expectation weighs `r(1, θ, R, ŵ)` by `p(1, θ, R, ŵ) / Pr(Pass = 1)`, so a null outcome contributes
`0`. Fixed seed and fixed `c`, since `P₀` depends on `E_c`. Parameters as in
`MayersQKD.sampling_bound`, which reads the paper's `γ = 10⁻⁶` and "appropriate `ε`". -/
theorem ratio_bound {n r m : ℕ} (δ ε γ : ℝ) (hδ : 0 ≤ δ) (hδε : δ < ε) (hγ : 0 < γ)
    (h6 : 6 * γ ≤ (ε - δ) ^ 2) (A : Attack n r m) (s : A.Seed) (c : Bool)
    (hP : (2 : ℝ) ^ (-(2 * γ * n)) <
      ∑ θ : Bases n, ∑ R : Finset (Fin n), ∑ what : Bits n, outcomeProb A δ s true θ R what) :
    (∑ θ : Bases n, ∑ R : Finset (Fin n), ∑ what : Bits n,
        outcomeProb A δ s true θ R what * ratioR A δ ε s c true θ R what) /
      (∑ θ : Bases n, ∑ R : Finset (Fin n), ∑ what : Bits n, outcomeProb A δ s true θ R what) ≤
    (2 : ℝ) ^ (-(2 * γ * n)) := by sorry

end MayersQKD
