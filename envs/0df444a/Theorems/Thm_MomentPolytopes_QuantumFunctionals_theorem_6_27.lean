-- Prove2me | Theorems.Thm_MomentPolytopes_QuantumFunctionals_theorem_6_27
-- name    : MomentPolytopes.QuantumFunctionals.theorem_6_27
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T01:05:35.861715+00:00
-- url     : https://prove2.me/theorems/1d8ce035-9c76-41c5-9acc-43284f24478d
-- title:
--   Theorem 6.27 — O(1/(ηk)) convergence of Hadamard mirror descent on the entanglement polytope; η = 1/(dL) for L-smooth ϕ
-- statement:
--   Let $0\ne T\in\mathrm{Ten}(n_0;n_1,\dots,n_d)$, and let $\phi:\mathbb R^{n_1}\times\dots\times\mathbb R^{n_d}\to\mathbb R\cup\{\infty\}$ satisfy (ϕ1)–(ϕ3) with $\operatorname{spec}\mu(g\cdot T)\in\operatorname{int}\operatorname{dom}\phi$ for all $g\in\mathrm{GL}(n_1)\times\dots\times\mathrm{GL}(n_d)$. Let $p^\star$ be a minimizer of $\phi$ on $\Delta(T)$.
--
--   1. For every step size $\eta>0$ and nonzero scalars $(c_k)$, if the Hadamard mirror descent sequence $(T_k)$ of (6.34) satisfies the step-size condition (6.17), then for all $k\ge1$
--   $$\phi(\operatorname{spec}\mu(T_k))-\min_{p\in\Delta(T)}\phi(p)\ \le\ \frac{2\big(\log\|T\|-\log\operatorname{Cap}_{p^\star}(T)\big)}{\eta k}.$$
--   2. Moreover, if $\phi$ is $L$-smooth ($L>0$, $d\ge1$), the step size $\eta=1/(dL)$ satisfies the step-size condition (6.17) for every choice of nonzero scalars.
--
--   Here $\log\operatorname{Cap}$ is the K-invariant logarithmic capacity with the Busemann normalization $b_X(I)=0$ and $\log$ is natural.
--
--   Differences from the source:
--   - encoding: ℓ ∈ [d] = {1, …, d} → ℓ : Fin d (0-based); reason: indexing convention; same instances
--   - encoding: ϕ : ℝ^{n_1} × ⋯ × ℝ^{n_d} → ℝ ∪ {∞} with (ϕ1)–(ϕ3) → ϕ : SpecTuple n → EReal with ϕ ≠ ⊥, lower semicontinuous, convex epigraph, permutation-symmetric, int dom nonempty, (ϕ p).toReal differentiable on int dom; reason: same class of functions
--   - encoding: ∇Φ, the Euclidean gradient of Φ = ϕ ∘ spec on H for the Hilbert–Schmidt inner product → hsGrad, read off from directional derivatives along the Hermitian basis E_aa, E_ab + E_ba, iE_ab − iE_ba; reason: equal wherever Φ is differentiable, which Proposition 3.6 gives on int dom Φ
--   - encoding: log Cap and log cap in [−∞, ∞) → EReal, −∞ = ⊥; the bound is an EReal inequality; reason: Lean convention; same values, no junk value for −∞
--   - generalization: Ten(n_0; n_1, …, n_d) with d ≥ 1 → any d : ℕ, including d = 0; reason: d = 0 is a degenerate case (trivial group, Δ(T) a point) where the claim holds; at d ≥ 1 the statement is the source's
--   - encoding: min_{p∈Δ(T)} ϕ(p) → ⨅ p ∈ Δ(T), ϕ p in EReal; reason: the infimum is attained at p⋆
--   - encoding: step size η (Definition 5.1, p. 24: η > 0); c_k ∈ ℂ^× → hypotheses 0 < η and c k ≠ 0; reason: standing assumptions made explicit
--   - reading: 'the step size can be taken as η = 1/(dL)' → for L-smooth ϕ the step-size condition (6.17) holds for (6.34) with η = 1/(dL) and every nonzero scalar sequence; reason: the proof (via Corollary 6.22, whose proof on p. 41 says 'the step-size condition is satisfied with our choice of η') establishes exactly this; part 1 then gives the bound
--   - encoding: η = 1/(dL) → hypotheses 0 < L and 0 < d in the Moreover clause; reason: 1/(dL) is undefined otherwise
--   - encoding: L-smooth: finite-valued with L-Lipschitz gradient → IsLSmooth: ϕ ≠ ⊤, (ϕ p).toReal differentiable, Euclidean gradient L-Lipschitz for the Euclidean norm; reason: same functions
-- source:
--   Doğan, Sakabe, Walter, Convex optimization on moment polytopes, arXiv:2609.06633 (PDF sha256 fcf40771…), p. 44, Theorem 6.27

import Mathlib
import Definitions.Def_MomentPolytopes_QuantumFunctionals_Spectra
import Definitions.Def_MomentPolytopes_QuantumFunctionals_TensorAction
import Definitions.Def_MomentPolytopes_QuantumFunctionals_EntanglementPolytope
import Definitions.Def_MomentPolytopes_QuantumFunctionals_MirrorDescent
import Definitions.Def_MomentPolytopes_QuantumFunctionals_Capacity

set_option autoImplicit false

open scoped ComplexOrder Matrix

namespace MomentPolytopes.QuantumFunctionals

/-- Theorem 6.27 (p. 44). For `0 ≠ T`, an objective `ϕ` with (ϕ1)–(ϕ3) and
`spec µ(g · T) ∈ int dom ϕ` for all `g`, and a minimizer `p⋆` of `ϕ` on `Δ(T)`:
(a) for every step size `η > 0` and nonzero scalars `c_k`, if the sequence (6.34) satisfies the
step-size condition (6.17), then for all `k ≥ 1`
`ϕ(spec µ(T_k)) − min_{p∈Δ(T)} ϕ(p) ≤ 2 (log‖T‖ − log Cap_{p⋆}(T)) / (ηk)`;
(b) if `ϕ` is `L`-smooth, the step size `η = 1/(dL)` satisfies the step-size condition. -/
theorem theorem_6_27 {d n0 : ℕ} {n : Fin d → ℕ} (T : Ten d n0 n) (hT : T ≠ 0)
    (ϕ : SpecTuple n → EReal) (hϕ : IsAdmissibleObjective ϕ)
    (hint : ∀ g : GTuple n, specTuple (momentMap (gact g T)) ∈ interior (effDom ϕ))
    (pstar : SpecTuple n) (hpstar : pstar ∈ entanglementPolytope T)
    (hmin : ∀ p ∈ entanglementPolytope T, ϕ pstar ≤ ϕ p) :
    (∀ (η : ℝ), 0 < η → ∀ c : ℕ → ℂ, (∀ k, c k ≠ 0) →
      StepSizeCondition ϕ η (mirrorDescentSeq ϕ η c T) c →
      ∀ k : ℕ, 1 ≤ k →
        ϕ (specTuple (momentMap (mirrorDescentSeq ϕ η c T k))) -
            ⨅ p ∈ entanglementPolytope T, ϕ p ≤
          ((2 : ℝ) : EReal) * ((Real.log (tnorm T) : EReal) - logCap pstar T) /
            ((η * k : ℝ) : EReal)) ∧
    (∀ L : ℝ, 0 < L → 0 < d → IsLSmooth ϕ L → ∀ c : ℕ → ℂ, (∀ k, c k ≠ 0) →
      StepSizeCondition ϕ (1 / (d * L)) (mirrorDescentSeq ϕ (1 / (d * L)) c T) c) := by sorry

end MomentPolytopes.QuantumFunctionals
