-- Prove2me | Theorems.Thm_HardCoreSpectral_AllFugacities_moderate_fugacity
-- name    : HardCoreSpectral.AllFugacities.moderate_fugacity
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-11T04:36:50.710193+00:00
-- url     : https://prove2.me/theorems/67d7d8d9-d3ea-482f-8958-9ac6a393c126
-- title:
--   Theorem 1.2 — FPRAS and efficient sampler for λ ≤ (1−ξ)/σ
-- statement:
--   With $\mathcal G^\sigma_{\Delta,\Delta}$, $Z_G$ and $\mu_{G,\lambda}$ as in the definitions item:
--
--   **Theorem 1.2.** Fix an integer $\Delta\ge3$, $\xi\in(0,1)$ and $\sigma>0$, and let $\lambda>0$ satisfy
--
--   $$
--   \lambda\le\frac{1-\xi}{\sigma}.
--   $$
--
--   Then there is an FPRAS for $Z_G(\lambda)$ and an efficient approximate sampler for $\mu_{G,\lambda}$ for every $G\in\mathcal G^\sigma_{\Delta,\Delta}$.
--
--   This is the moderate-fugacity half of Theorem 1.1, proved by discrete quadratic localization.
--
--   **Formalization Note.** The class, the hard-core model and the FPRAS/FPTAS/sampler predicates are those of `HardCoreSpectral.AllFugacities.Approximation`, stated over the register machine of `HardCoreSpectral.AllFugacities.RegisterMachine`. In each predicate a single program and a single polynomial budget are chosen after the theorem's fixed parameters and before the graph and the accuracy $\varepsilon\in(0,1)$; the fixed real parameters are passed to the program as input. Here the fixed real parameters passed are $\lambda,\sigma,\xi$.
--
--   Differences from the source:
--   - reading: an algorithm running in time polynomial in |V(G)| and 1/ε (no machine model specified) → a finite register-machine program with rational literals, unit-cost real arithmetic, sqrt, exp, log, comparisons, adjacency queries and uniform [0,1] draws, halting without fault on every tape within C(2n+⌈1/ε⌉)^d steps, with C, d fixed before the graph and ε; reason: the paper's pseudocode is stated over real parameters; this is the real-register reading the mission brief prescribes, with worst-case runtime
--   - encoding: the fixed real parameters of the theorem (λ, σ, ...) are fixed data of the algorithm → they are passed to the program as input parameters after ε; reason: program literals are rational; the program is still chosen after these parameters, so no instance changes
--   - encoding: G ∈ 𝒢^σ_{Δ,Δ} on L ⊔ R with |L| = |R| = n; σ₂(M_G) ≤ σ → a Boolean biadjacency matrix on Fin n × Fin n, input as the 2n × 2n adjacency matrix with L first; ‖Π⊥ M Π⊥ x‖² ≤ σ²‖x‖² for all x, with 0 ≤ σ; reason: every such graph is one of these up to relabelling; σ₂(M) = ‖Π⊥MΠ⊥‖_op is the identity stated on p. 6
--   - generalization: graphs with n vertices per side, implicitly n ≥ 1 → n = 0 (the empty graph, vacuously Δ-regular) is also admitted; reason: for n ≥ 1 regularity forces n ≥ Δ exactly as in the source; the extra n = 0 instance has Z = 1 and only adds a trivial case
--   - encoding: the output is an estimate Ẑ, respectively an independent set with law μ̂ → register 0, respectively the vertices whose memory cell is nonzero, after the budgeted run; the sampler is also required to output an independent set on every run, and the output events are required to be measurable; reason: a fixed output convention; every event of this machine is Borel in the tape, so the measurability clause excludes no program
-- source:
--   Ijay Narang, Will Perkins, STOC 2027 submission #294 (October 2026), Theorem 1.2, p. 3 (PDF p. 3).

import Mathlib
import Definitions.Def_HardCoreSpectral_AllFugacities_RegisterMachine
import Definitions.Def_HardCoreSpectral_AllFugacities_Approximation

set_option autoImplicit false

namespace HardCoreSpectral.AllFugacities

/-- Theorem 1.2 (p. 3). For an integer `Δ ≥ 3`, `ξ ∈ (0,1)`, `σ > 0` and `0 < λ ≤ (1 − ξ)/σ`
there is an FPRAS for `Z_G(λ)` and an efficient approximate sampler for `μ_{G,λ}` on
`𝒢^σ_{Δ,Δ}`. -/
theorem moderate_fugacity (Δ : ℕ) (hΔ : 3 ≤ Δ) (ξ : ℝ) (hξ0 : 0 < ξ) (hξ1 : ξ < 1)
    (σ : ℝ) (hσ : 0 < σ) (lam : ℝ) (hlam : 0 < lam) (hlamσ : lam ≤ (1 - ξ) / σ) :
    IsFPRAS Δ σ lam [lam, σ, ξ] ∧ IsEfficientSampler Δ σ lam [lam, σ, ξ] := by sorry

end HardCoreSpectral.AllFugacities
