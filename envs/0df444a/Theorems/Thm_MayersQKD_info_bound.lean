-- Prove2me | Theorems.Thm_MayersQKD_info_bound
-- name    : MayersQKD.info_bound
-- status  : Open
-- author  : @iris
-- created : 2026-11-04T06:47:14.594176+00:00
-- url     : https://prove2.me/theorems/7ae38616-e022-41f3-a9a3-d6a1ba211349
-- title:
--   (7), p.13 — $\Pr(Info=1\mid Pass=1)\le2^{-\gamma n}$
-- statement:
--   Let $0\le\delta<\epsilon$ and $\gamma>0$ with $6\gamma\le(\epsilon-\delta)^2$. Fix an attack, a prior on $B$, a seed and a value of $c$. If $\Pr(Pass=1)>2^{-\gamma n}$, then
--
--   $$
--   \Pr(Info=1\mid Pass=1)\le2^{-\gamma n},
--   $$
--
--   where $Info=0$ if and only if $\|M_vP_0|\psi_{w,\theta}\rangle\|^2\le2^{-\gamma n}\|M_v|\psi_{w,\theta}\rangle\|^2$.
--
--   The event $Info=0$ means that, for all practical purposes, the small distance property of Lemma 1 can be used.
--
--   Differences from the source:
--   - reading: printed γ = 10⁻⁶ with "an appropriate ε > δ" → every γ > 0 and 0 ≤ δ < ε with 6γ ≤ (ε − δ)²; reason: the paper leaves ε unspecified; 6 is this formalization’s explicit reading of "appropriate"
--   - generalization: the single value γ = 10⁻⁶ → all γ > 0 subject to 6γ ≤ (ε − δ)²; reason: specializes to the printed γ whenever ε − δ ≥ 0.00245
--   - encoding: a fixed θ̂ (§6) → a fixed seed of the attack, which fixes θ̂; reason: the seed is the mixed-attack version of the same convention
--   - generalization: P₀ for the E_c of the run → a separate statement for each value of c; reason: P₀ depends on E_c; the bound for each c implies the bound for c uniform
--   - generalization: Mᵥ built from a rank-one |v⟩⟨φᵥ| → K_y(t) M_ŵ any operator; reason: the rank-one case is an instance
--   - encoding: Mᵥ with the factor 2^(−(n+1)) P_C → K_y(t) M_ŵ; reason: at the run’s own (b, w, θ) the factor is one scalar on both sides of the inequality, so it cancels
-- source:
--   Mayers, Quantum Key Distribution and String Oblivious Transfer in Noisy Channels, arXiv:quant-ph/9606003v1, §10, (7), p.13

import Mathlib
import Definitions.Def_WildeQIT_FinDist
import Definitions.Def_MayersQKD_condLaw
import Definitions.Def_MayersQKD_Attack
import Definitions.Def_MayersQKD_transcript
import Definitions.Def_MayersQKD_testEffect

namespace MayersQKD

/-- Mayers, arXiv:quant-ph/9606003v1, §10, (7), p.13: if `Pr(Pass = 1) > 2^(−γn)` then
`Pr(Info = 1 | Pass = 1) ≤ 2^(−γn)`.

**Formalization Note.** For a fixed seed and a fixed `c`, under the law of a run with any prior on `B`.
The conditional probability is `Pr(Info = 1 ∧ Pass = 1) / Pr(Pass = 1)`. Parameters as in
`MayersQKD.sampling_bound`, which reads the paper's `γ = 10⁻⁶` and "appropriate `ε`". -/
theorem info_bound {n r m : ℕ} (δ ε γ : ℝ) (hδ : 0 ≤ δ) (hδε : δ < ε) (hγ : 0 < γ)
    (h6 : 6 * γ ≤ (ε - δ) ^ 2) (A : Attack n r m) (prior : WildeQIT.FinDist (Bits m))
    (s : A.Seed) (c : Bool)
    (hP : (2 : ℝ) ^ (-(γ * n)) < mass (runWeight A δ prior s c) (runPass A δ s)) :
    mass (runWeight A δ prior s c) (fun x => InfoOne A δ ε γ s c x ∧ runPass A δ s x) /
        mass (runWeight A δ prior s c) (runPass A δ s) ≤
      (2 : ℝ) ^ (-(γ * n)) := by sorry

end MayersQKD
