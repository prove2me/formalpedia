-- Prove2me | Theorems.Thm_GoodProphets_lemma_3_2
-- name    : GoodProphets.lemma_3_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-04T06:25:10.872777+00:00
-- url     : https://prove2.me/theorems/a806465e-0030-4e94-9b3b-1d13979d02f6
-- title:
--   Lemma 3.2 — w.p. $\ge1-2kT^{-T^\epsilon/\delta^2}$ an optimal clairvoyant solution has $\mathrm{OPT}_{\theta j}\ge T\,\mathrm{DLP}_{\theta j}-[T\log T]^{(1+\epsilon)/2}$
-- statement:
--   Let the instance satisfy property (ii) of Proposition 1 with a constant $\delta>0$, and let $\epsilon>0$. Let $\mathrm{DLP}$ be an optimal solution of the deterministic linear program $\min_{\vec x\ge0}f_{\vec p}(\vec x)$, in which the arrival probabilities $\vec p$ stand in for the counts. Let $T\ge1$ arrivals be i.i.d. with distribution $\vec p$, with counts $\vec N$. Then with probability at least
--   $$
--   1-2k\,T^{-T^\epsilon/\delta^2}
--   $$
--   there is an optimal clairvoyant solution $\mathrm{OPT}\in\arg\min_{\vec x\ge0}f_{\vec N}(\vec x)$ such that, for every action $a_{\theta j}$,
--   $$
--   \mathrm{OPT}_{\theta j}\ \ge\ T\times\mathrm{DLP}_{\theta j}-[T\log(T)]^{\frac{1+\epsilon}2}.
--   $$
--   Before the horizon is known, the algorithm can safely take each action about $T\times\mathrm{DLP}_{\theta j}$ times. This lemma is what justifies that.
--
--   **Formalization Note** $\log$ is natural and the power is `Real.rpow`. The claim is stated for every optimal solution of the DLP.
--
--   Differences from the source:
--   - reading: OPT_θj, the clairvoyant's solution → some optimal clairvoyant solution x⋆ ∈ argmin_{x≥0} f_N satisfies the bound; reason: the lemma names no selection and its proof obtains the solution from Proposition 1 (ii), an existence statement; the paper's own Lemma C.2 (p.31) uses this wording; the stronger forms fail under the paper's assumptions: k = 1, ℓ = 2, f ≡ 0, d = (1, 0) has the optimal x⋆ = (0, T), and a rule with σ(1, 0) = (1, 0), σ(T, 0) = (0, T) is a valid selection, since Assumption 2 compares only right-hand sides of equal total
--   - generalization: DLP, the selected optimal solution of min_{x≥0} f_p → every optimal solution d of min_{x≥0} f_p; reason: the selected solution is one of them
--   - encoding: δ, the constant of Proposition 1 (ii), in the exponent −T^ε/δ² → 0 < δ and StabHyp I δ; reason: the bound divides by δ²; δ ≤ 0 is excluded as undefined
--   - generalization: the standing assumptions of §2 and Assumption 3 (p_θ ≥ β > 0; f_N real-valued; ε < 1/2) → any probability vector p; no boundedness hypothesis; every ε > 0; reason: the statement does not need them; it specializes to the paper's setting
--   - generalization: Proposition 1 (ii) "for any y, any N and N′" → StabHyp I δ: only for y ≥ 0, N, N′ ≥ 0 with both feasible sets non-empty; reason: a weaker hypothesis; the proof applies (ii) at y = 0, N = Tp, N′ = the counts, where both sets are non-empty
--   - encoding: the horizon T → 1 ≤ T; reason: a horizon has at least one period
-- source:
--   S. Banerjee and D. Freund, Good prophets know when the end is near, Management Science (2024), doi:10.1287/mnsc.2023.04307 (author manuscript, sha256 2cfd1ada…2c46), Lemma 3.2, p.11 (proof p.26, A.2)

import Mathlib
import Definitions.Def_GoodProphets_StabHyp
import Definitions.Def_GoodProphets_seqProb

namespace GoodProphets

/-- **Lemma 3.2** (Banerjee & Freund, *Good prophets know when the end is near*, Management
Science (2024), doi:10.1287/mnsc.2023.04307 (author manuscript), p.11): "With probability at least
`1 − 2k T^{−T^ε/δ²}` we have for every action `a_θj` that
`OPT_θj ≥ T × DLP_θj − [T log(T)]^{(1+ε)/2}`."

Here `δ > 0` is a constant for which Proposition 1 (ii) holds (`StabHyp I δ`), `ε > 0`, the `T ≥ 1`
arrivals are i.i.d. from the probability vector `p`, `DLP` is an optimal solution `d` of the
deterministic LP `min_{x ≥ 0} f_p(x)` (p.10), and `OPT` is an optimal solution of the clairvoyant
problem `min_{x ≥ 0} f_N(x)` for the realized counts `N`.

**Formalization Note** "`OPT_θj ≥ …`" is read as "some optimal clairvoyant solution `x⋆`
satisfies `x⋆_θj ≥ …` for every `θ, j`" (the lemma names no selection; cf. the paper's own wording
"there exists some solution" in Lemma C.2, p.31). The statement holds for every optimal solution `d`
of the DLP, in particular the selected one. `log` is natural and `[·]^{(1+ε)/2}` is `Real.rpow`. -/
theorem lemma_3_2 {k ℓ r m : ℕ} (I : Instance k ℓ r m) (δ ε : ℝ) (hδ : 0 < δ) (hε : 0 < ε)
    (hstab : StabHyp I δ) (p : Fin k → ℝ) (hp0 : ∀ θ, 0 ≤ p θ) (hp1 : ∑ θ, p θ = 1)
    (d : Fin k → Fin ℓ → ℝ) (hd : IsOptIn I p 0 d) (T : ℕ) (hT : 1 ≤ T) :
    1 - 2 * k * (T : ℝ) ^ (-((T : ℝ) ^ ε / δ ^ 2)) ≤
      seqProb p (fun θs : Fin T → Fin k => ∃ xstar : Fin k → Fin ℓ → ℝ,
        IsOptIn I (fun θ => (countAll θs θ : ℝ)) 0 xstar ∧
          ∀ θ j, (T : ℝ) * d θ j - ((T : ℝ) * Real.log T) ^ ((1 + ε) / 2) ≤ xstar θ j) := by sorry

end GoodProphets
