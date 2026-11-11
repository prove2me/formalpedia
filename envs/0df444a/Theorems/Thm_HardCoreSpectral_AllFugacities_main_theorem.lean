-- Prove2me | Theorems.Thm_HardCoreSpectral_AllFugacities_main_theorem
-- name    : HardCoreSpectral.AllFugacities.main_theorem
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-11T04:37:00.597624+00:00
-- url     : https://prove2.me/theorems/172e68bd-c790-4b97-829e-04b8f16e6e45
-- title:
--   Theorem 1.1 — FPRAS and efficient sampler for the hard-core model on spectral bipartite expanders at every fugacity
-- statement:
--   Let $\mathcal G^\sigma_{\Delta,\Delta}$ be the class of $\Delta$-regular bipartite graphs $G$ on $L\sqcup R$, $|L|=|R|=n$, whose biadjacency matrix has second-largest singular value $\sigma_2(M_G)\le\sigma$. For $\lambda>0$ let $Z_G(\lambda)=\sum_{I\in\mathcal I(G)}\lambda^{|I|}$ and $\mu_{G,\lambda}(I)=\lambda^{|I|}/Z_G(\lambda)$ be the hard-core partition function and measure.
--
--   **Theorem 1.1.** There are absolute constants $c>0$ and $\Delta_0\ge 3$ such that, for every integer $\Delta\ge\Delta_0$ and every $\sigma\ge0$ with
--
--   $$
--   \sigma\le c\left(\frac{\Delta^2}{\log(e\Delta)}\right)^{1/3},
--   $$
--
--   and every fugacity $\lambda>0$, there is an FPRAS for $Z_G(\lambda)$ and an efficient approximate sampler for $\mu_{G,\lambda}$ on $\mathcal G^\sigma_{\Delta,\Delta}$: for every $G$ in the class and every $\varepsilon\in(0,1)$, in time polynomial in $|V(G)|$ and $1/\varepsilon$, the first outputs a $(1\pm\varepsilon)$-approximation of $Z_G(\lambda)$ with probability at least $3/4$, and the second outputs an independent set whose law is at total variation distance less than $\varepsilon$ from $\mu_{G,\lambda}$.
--
--   This is the paper's main result: a spectral condition on the nontrivial singular values alone, efficiently checkable, certifies approximate counting and sampling at all fugacities, combining the moderate-fugacity Theorem 1.2 and the high-fugacity Theorem 1.3.
--
--   **Formalization Note.** The class, the hard-core model and the FPRAS/FPTAS/sampler predicates are those of `HardCoreSpectral.AllFugacities.Approximation`, stated over the register machine of `HardCoreSpectral.AllFugacities.RegisterMachine`. In each predicate a single program and a single polynomial budget are chosen after the theorem's fixed parameters and before the graph and the accuracy $\varepsilon\in(0,1)$; the fixed real parameters are passed to the program as input.
--
--   Differences from the source:
--   - reading: an algorithm running in time polynomial in |V(G)| and 1/ε (no machine model specified) → a finite register-machine program with rational literals, unit-cost real arithmetic, sqrt, exp, log, comparisons, adjacency queries and uniform [0,1] draws, halting without fault on every tape within C(2n+⌈1/ε⌉)^d steps, with C, d fixed before the graph and ε; reason: the paper's pseudocode is stated over real parameters; this is the real-register reading the mission brief prescribes, with worst-case runtime
--   - encoding: the fixed real parameters of the theorem (λ, σ, ...) are fixed data of the algorithm → they are passed to the program as input parameters after ε; reason: program literals are rational; the program is still chosen after these parameters, so no instance changes
--   - encoding: G ∈ 𝒢^σ_{Δ,Δ} on L ⊔ R with |L| = |R| = n; σ₂(M_G) ≤ σ → a Boolean biadjacency matrix on Fin n × Fin n, input as the 2n × 2n adjacency matrix with L first; ‖Π⊥ M Π⊥ x‖² ≤ σ²‖x‖² for all x, with 0 ≤ σ; reason: every such graph is one of these up to relabelling; σ₂(M) = ‖Π⊥MΠ⊥‖_op is the identity stated on p. 6
--   - encoding: absolute constant Δ₀ ≥ 3 and every Δ ≥ Δ₀ (Δ a degree) → Δ₀ : ℕ with 3 ≤ Δ₀; reason: Δ is an integer, so a real threshold Δ₀ can be replaced by ⌈Δ₀⌉
--   - generalization: graphs with n vertices per side, implicitly n ≥ 1 → n = 0 (the empty graph, vacuously Δ-regular) is also admitted; reason: for n ≥ 1 regularity forces n ≥ Δ exactly as in the source; the extra n = 0 instance has Z = 1 and only adds a trivial case
--   - encoding: the output is an estimate Ẑ, respectively an independent set with law μ̂ → register 0, respectively the vertices whose memory cell is nonzero, after the budgeted run; the sampler is also required to output an independent set on every run, and the output events are required to be measurable; reason: a fixed output convention; every event of this machine is Borel in the tape, so the measurability clause excludes no program
-- source:
--   Ijay Narang, Will Perkins, STOC 2027 submission #294 (October 2026), Theorem 1.1, p. 3 (PDF p. 3).

import Mathlib
import Definitions.Def_HardCoreSpectral_AllFugacities_RegisterMachine
import Definitions.Def_HardCoreSpectral_AllFugacities_Approximation

set_option autoImplicit false

namespace HardCoreSpectral.AllFugacities

/-- Theorem 1.1 (p. 3). Absolute constants `c > 0`, `Δ₀ ≥ 3`; for every `Δ ≥ Δ₀`, every
certificate `0 ≤ σ ≤ c (Δ² / log(eΔ))^{1/3}` and every fugacity `λ > 0` there is an FPRAS for
`Z_G(λ)` and an efficient approximate sampler for `μ_{G,λ}` on `𝒢^σ_{Δ,Δ}`. -/
theorem main_theorem :
    ∃ c : ℝ, 0 < c ∧ ∃ Δ₀ : ℕ, 3 ≤ Δ₀ ∧
      ∀ Δ : ℕ, Δ₀ ≤ Δ → ∀ σ : ℝ, 0 ≤ σ →
        σ ≤ c * ((Δ : ℝ) ^ 2 / Real.log (Real.exp 1 * Δ)) ^ ((1 : ℝ) / 3) →
        ∀ lam : ℝ, 0 < lam →
          IsFPRAS Δ σ lam [lam, σ] ∧ IsEfficientSampler Δ σ lam [lam, σ] := by sorry

end HardCoreSpectral.AllFugacities
