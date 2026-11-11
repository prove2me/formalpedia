-- Prove2me | Theorems.Thm_LimitedEntanglementTomography_LowerBound_proposition_6_1
-- name    : LimitedEntanglementTomography.LowerBound.proposition_6_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T07:13:03.790252+00:00
-- url     : https://prove2.me/theorems/02d2ac90-3569-4ae0-8adb-ed7f76502335
-- title:
--   Proposition 6.1 — properties (41)–(44) of the truncated Gaussian prior
-- statement:
--   There is an absolute $C_1\ge2$, an absolute $c>0$ and $d_0$ such that every $C_*\ge C_1$ is an admissible choice of the constant $C_*$ of §6.1: for every $C_*\ge C_1$, every $d\ge d_0$ and every $\varepsilon>0$, with $\tau=C_*\varepsilon$, $\kappa=d^3/(2\tau^2)$, $K=\{\Delta\in\mathrm{Herm}_0(\mathbb C^d):\|\Delta\|_{\mathrm{op}}\le C_*\tau/d\}$, $\bar\mu$ the centered Gaussian with covariance $\kappa^{-1}I$ and $\mu=\bar\mu(\cdot\mid K)$:
--
--   1. the conditioning event has probability $\bar\mu(K)\ge\tfrac12$;
--   2. if $\varepsilon\le1/(2C_*^2)$, then for every $\Delta\in K$ the matrix $I_d/d+\Delta$ is a state and $I_d/d+\Delta\succeq I_d/(2d)$;
--   3. every positive smooth $f$ with $\mathbb E_\mu f=1$ satisfies
--   $$\mathrm{Ent}_\mu(f)\le\frac1{2\kappa}\,\mathbb E_\mu\Big[\frac{\|\nabla f\|_2^2}{f}\Big]=\frac{\tau^2}{d^3}\,\mathbb E_\mu\Big[\frac{\|\nabla f\|_2^2}{f}\Big];$$
--   4. uniformly over $\Delta_0\in\mathrm{Herm}_0(\mathbb C^d)$,
--   $$-\log\mu\{\Delta:\|\Delta-\Delta_0\|_1\le2\varepsilon\}\ge c\,d^2 .$$
--
--   Items 2 and 3 feed the information upper bound (Proposition 7.1), item 4 the information lower bound (Corollary 6.2).
--
--   Differences from the source:
--   - generalization: one absolute C_* ≥ 2 fixed in Proposition 6.1 and used for the rest of the paper → every C_* ≥ C₁ for one absolute C₁ ≥ 2, with the remaining constants (c, d₀) uniform in C_*; reason: the proof of Proposition 6.1 uses only C_*/√2 ≥ C₀ and √2/C_* ≤ c₀/2, both monotone in C_*; taking C_* = C₁ recovers the source statement, and the uniformity lets Proposition 6.1, Corollary 6.2 and the main proof share one C_*
--   - encoding: −log μ(B) ≳ d² → μ(B) ≤ e^{−c d²} with c absolute; reason: equivalent, with −log 0 = +∞ as the extended meaning at probability zero
--   - encoding: Ent_μ(f) and E_μ[‖∇f‖²/f] as real numbers → both in [0,∞], Ent written as E[f log f − f + 1] under E f = 1; reason: equal when E f = 1, no integrability hypothesis added
--   - encoding: one fixed Frobenius-orthonormal basis F_1,…,F_{d²−1} of Herm₀(ℂ^d) → the statement holds for every orthonormal basis F (IsHerm0ONB F); reason: the source fixes an arbitrary such basis, so its claim is the same claim for every basis; trace Fisher information and the standard Gaussian law do not depend on the basis
--   - encoding: random matrices and sets in Herm₀(ℂ^d) → coordinates θ ∈ ℝ^{d²−1} with Δ = ∑_b θ_b F_b (herm0Coord); reason: an isometric linear bijection for the Frobenius norm; laws and events correspond one to one
--   - encoding: probabilities and expectations of nonnegative quantities in ℝ → values of measures in [0,∞] (ENNReal); reason: a probability is the same number; inequalities are unchanged
-- source:
--   Ufuk Keskin, Jason Luo, Mahbod Majid, Matthew Radzihovsky, Tight Lower Bounds for State Tomography with Limited Entanglement, STOC 2027 submission #1625 (October 2026), source.pdf SHA-256 bdd8884c95899a0c563507d1c005e0dee86e418d52478a2e9e6682bb1f9d29c3, https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1625.pdf, §6.1, printed p.23 / PDF p.25, Proposition 6.1 (eqs. (41)–(44))

import Mathlib
import Definitions.Def_LimitedEntanglementTomography_LowerBound_Prior

open scoped ENNReal ComplexOrder

/-!
Ufuk Keskin, Jason Luo, Mahbod Majid, Matthew Radzihovsky, *Tight Lower Bounds for State
Tomography with Limited Entanglement*, STOC 2027 submission #1625 (October 2026), Proposition 6.1, printed p.23 / PDF p.25, eqs. (41)–(44).
-/

namespace LimitedEntanglementTomography.LowerBound

open MeasureTheory ProbabilityTheory Matrix ShadowTomography.ClassicalLB

/-- **Proposition 6.1.** There is an absolute `C₁ ≥ 2` (every `C_* ≥ C₁` is an admissible choice
of `C_*`), an absolute `c > 0` and `d₀` such that for every `C_* ≥ C₁`, every `d ≥ d₀`, every
`ε > 0` (with `τ = C_* ε`, `κ = d³/(2τ²)`, `K = {Δ ∈ Herm₀ : ‖Δ‖_op ≤ C_* τ/d}`, `μ̄` the centered
Gaussian of covariance `κ⁻¹ I` and `μ = μ̄(· | K)`):
1. `μ̄(K) ≥ 1/2` (41);
2. if `ε ≤ 1/(2C_*²)`, then for every `Δ ∈ K`, `I_d/d + Δ` is a state and `I_d/d + Δ ⪰ I_d/(2d)` (42);
3. every positive smooth `f` with `E_μ f = 1` has
   `Ent_μ(f) ≤ (1/(2κ)) E_μ[‖∇f‖²/f]`, and `1/(2κ) = τ²/d³` (43);
4. uniformly over `Δ₀ ∈ Herm₀(ℂ^d)`, `−log μ{Δ : ‖Δ − Δ₀‖₁ ≤ 2ε} ≥ c d²`, i.e.
   `μ{Δ : ‖Δ − Δ₀‖₁ ≤ 2ε} ≤ e^{−c d²}` (44). -/
theorem proposition_6_1 :
    ∃ C₁ : ℝ, 2 ≤ C₁ ∧ ∃ c : ℝ, 0 < c ∧ ∃ d₀ : ℕ,
      ∀ Cstar : ℝ, C₁ ≤ Cstar → ∀ d : ℕ, d₀ ≤ d → ∀ ε : ℝ, 0 < ε →
      ∀ F : Fin (d ^ 2 - 1) → Op d, IsHerm0ONB F →
        ENNReal.ofReal (1 / 2) ≤ priorBar d Cstar ε (priorK F Cstar ε) ∧
        (ε ≤ 1 / (2 * Cstar ^ 2) → ∀ θ ∈ priorK F Cstar ε,
          WildeQIT.IsDensityOperator (((1 / (d : ℝ) : ℝ) : ℂ) • (1 : Op d) + herm0Coord F θ) ∧
          LoewnerGE (((1 / (d : ℝ) : ℝ) : ℂ) • (1 : Op d) + herm0Coord F θ) (1 / (2 * (d : ℝ)))) ∧
        (∀ f : Coord (d ^ 2 - 1) → ℝ, (∀ x, 0 < f x) → ContDiff ℝ (⊤ : ℕ∞) f →
          ∫⁻ x, ENNReal.ofReal (f x) ∂(prior F Cstar ε) = 1 →
          entropy (prior F Cstar ε) f ≤
            ENNReal.ofReal (1 / (2 * priorKappa d Cstar ε)) * fisherFunctional (prior F Cstar ε) f) ∧
        1 / (2 * priorKappa d Cstar ε) = (Cstar * ε) ^ 2 / (d : ℝ) ^ 3 ∧
        (∀ θ₀ : Coord (d ^ 2 - 1),
          prior F Cstar ε {θ | traceNorm (herm0Coord F θ - herm0Coord F θ₀) ≤ 2 * ε} ≤
            ENNReal.ofReal (Real.exp (-(c * (d : ℝ) ^ 2)))) := by sorry

end LimitedEntanglementTomography.LowerBound
