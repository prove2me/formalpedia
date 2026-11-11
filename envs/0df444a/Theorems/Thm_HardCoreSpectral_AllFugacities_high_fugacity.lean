-- Prove2me | Theorems.Thm_HardCoreSpectral_AllFugacities_high_fugacity
-- name    : HardCoreSpectral.AllFugacities.high_fugacity
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-11T04:37:06.240475+00:00
-- url     : https://prove2.me/theorems/2b9a1be1-4100-4f31-ab2d-a6ff484ecb0e
-- title:
--   Theorem 1.3 — FPTAS and efficient sampler for λ ≥ exp(Cσ²log(eΔ)/(Δ²−σ²)) − 1
-- statement:
--   With $\mathcal G^\sigma_{\Delta,\Delta}$, $Z_G$ and $\mu_{G,\lambda}$ as in the definitions item:
--
--   **Theorem 1.3.** There is an absolute constant $C>0$ such that, for every integer $\Delta\ge3$, every $0\le\sigma<\Delta$ and every $\lambda>0$ with
--
--   $$
--   \lambda\ge\exp\left[C\,\frac{\sigma^2}{\Delta^2-\sigma^2}\log(e\Delta)\right]-1,
--   $$
--
--   there is an FPTAS for $Z_G(\lambda)$ and an efficient approximate sampler for $\mu_{G,\lambda}$ for every $G\in\mathcal G^\sigma_{\Delta,\Delta}$.
--
--   This is the high-fugacity half of Theorem 1.1, proved with spectrally certified two-phase polymer models.
--
--   **Formalization Note.** The class, the hard-core model and the FPRAS/FPTAS/sampler predicates are those of `HardCoreSpectral.AllFugacities.Approximation`, stated over the register machine of `HardCoreSpectral.AllFugacities.RegisterMachine`. In each predicate a single program and a single polynomial budget are chosen after the theorem's fixed parameters and before the graph and the accuracy $\varepsilon\in(0,1)$; the fixed real parameters are passed to the program as input. The FPTAS is a program without uniform-draw instructions; here the fixed real parameters passed are $\lambda,\sigma$.
--
--   Differences from the source:
--   - reading: an algorithm running in time polynomial in |V(G)| and 1/ε (no machine model specified) → a finite register-machine program with rational literals, unit-cost real arithmetic, sqrt, exp, log, comparisons, adjacency queries and uniform [0,1] draws, halting without fault on every tape within C(2n+⌈1/ε⌉)^d steps, with C, d fixed before the graph and ε; reason: the paper's pseudocode is stated over real parameters; this is the real-register reading the mission brief prescribes, with worst-case runtime
--   - encoding: the fixed real parameters of the theorem (λ, σ, ...) are fixed data of the algorithm → they are passed to the program as input parameters after ε; reason: program literals are rational; the program is still chosen after these parameters, so no instance changes
--   - encoding: G ∈ 𝒢^σ_{Δ,Δ} on L ⊔ R with |L| = |R| = n; σ₂(M_G) ≤ σ → a Boolean biadjacency matrix on Fin n × Fin n, input as the 2n × 2n adjacency matrix with L first; ‖Π⊥ M Π⊥ x‖² ≤ σ²‖x‖² for all x, with 0 ≤ σ; reason: every such graph is one of these up to relabelling; σ₂(M) = ‖Π⊥MΠ⊥‖_op is the identity stated on p. 6
--   - generalization: graphs with n vertices per side, implicitly n ≥ 1 → n = 0 (the empty graph, vacuously Δ-regular) is also admitted; reason: for n ≥ 1 regularity forces n ≥ Δ exactly as in the source; the extra n = 0 instance has Z = 1 and only adds a trivial case
--   - encoding: the output is an estimate Ẑ, respectively an independent set with law μ̂ → register 0, respectively the vertices whose memory cell is nonzero, after the budgeted run; the sampler is also required to output an independent set on every run, and the output events are required to be measurable; reason: a fixed output convention; every event of this machine is Borel in the tape, so the measurability clause excludes no program
-- source:
--   Ijay Narang, Will Perkins, STOC 2027 submission #294 (October 2026), Theorem 1.3, pp. 3–4 (PDF pp. 3–4).

import Mathlib
import Definitions.Def_HardCoreSpectral_AllFugacities_RegisterMachine
import Definitions.Def_HardCoreSpectral_AllFugacities_Approximation

set_option autoImplicit false

namespace HardCoreSpectral.AllFugacities

/-- Theorem 1.3 (pp. 3–4). An absolute `C > 0` such that for every integer `Δ ≥ 3`,
`0 ≤ σ < Δ` and `λ > 0` with `λ ≥ exp(C σ²/(Δ² − σ²) · log(eΔ)) − 1` there is an FPTAS for
`Z_G(λ)` and an efficient approximate sampler for `μ_{G,λ}` on `𝒢^σ_{Δ,Δ}`. -/
theorem high_fugacity :
    ∃ C : ℝ, 0 < C ∧
      ∀ Δ : ℕ, 3 ≤ Δ → ∀ σ : ℝ, 0 ≤ σ → σ < Δ → ∀ lam : ℝ, 0 < lam →
        Real.exp (C * (σ ^ 2 / ((Δ : ℝ) ^ 2 - σ ^ 2)) * Real.log (Real.exp 1 * Δ)) - 1 ≤ lam →
        IsFPTAS Δ σ lam [lam, σ] ∧ IsEfficientSampler Δ σ lam [lam, σ] := by sorry

end HardCoreSpectral.AllFugacities
