-- Prove2me | Theorems.Thm_MomentPolytopes_QuantumFunctionals_theorem_6_28
-- name    : MomentPolytopes.QuantumFunctionals.theorem_6_28
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T01:05:28.60735+00:00
-- url     : https://prove2.me/theorems/ff3f4b10-ce9e-410c-8e27-aae751d36f0e
-- title:
--   Theorem 6.28 — −log Cap_p(T) ≤ poly(d, n_max) for Gaussian-integer T and p ∈ Δ(T); hence the Theorem 6.27 gap is ≤ poly(d, n_max, ⟨T⟩)/(ηk)
-- statement:
--   Let $n_{\max}=\max_\ell n_\ell$ and let $\langle T\rangle$ be the bit-length of $T$.
--
--   1. There is one polynomial bound $C(1+d+n_{\max})^c$ such that for all $d,n_0,n_1,\dots,n_d$, every nonzero tensor tuple $T$ with Gaussian integer entries and every $p\in\Delta(T)$,
--   $$-\log\operatorname{Cap}_p(T)\ \le\ C(1+d+n_{\max})^c .$$
--   2. Accordingly, Theorem 6.27 holds with a polynomial bound: there is one $C'(1+d+n_{\max}+\langle T\rangle)^{c'}$ such that whenever $T\ne0$ has Gaussian integer entries, $\phi$ satisfies (ϕ1)–(ϕ3) with $\operatorname{spec}\mu(g\cdot T)\in\operatorname{int}\operatorname{dom}\phi$ for all $g$, $\eta>0$, the scalars $c_k$ are nonzero and the sequence (6.34) satisfies the step-size condition (6.17), then for all $k\ge1$
--   $$\phi(\operatorname{spec}\mu(T_k))-\min_{p\in\Delta(T)}\phi(p)\ \le\ \frac1{\eta k}\,C'(1+d+n_{\max}+\langle T\rangle)^{c'} .$$
--
--   The first bound is independent of $n_0$ and of the size of the entries; it makes the convergence of Hadamard mirror descent polynomial in the input bit-length.
--
--   Differences from the source:
--   - encoding: ℓ ∈ [d] = {1, …, d} → ℓ : Fin d (0-based); reason: indexing convention; same instances
--   - encoding: log Cap and log cap in [−∞, ∞) → EReal, −∞ = ⊥; the bound is an EReal inequality; reason: Lean convention; same values, no junk value for −∞
--   - encoding: ϕ : ℝ^{n_1} × ⋯ × ℝ^{n_d} → ℝ ∪ {∞} with (ϕ1)–(ϕ3) → ϕ : SpecTuple n → EReal with ϕ ≠ ⊥, lower semicontinuous, convex epigraph, permutation-symmetric, int dom nonempty, (ϕ p).toReal differentiable on int dom; reason: same class of functions
--   - encoding: ∇Φ, the Euclidean gradient of Φ = ϕ ∘ spec on H for the Hilbert–Schmidt inner product → hsGrad, read off from directional derivatives along the Hermitian basis E_aa, E_ab + E_ba, iE_ab − iE_ba; reason: equal wherever Φ is differentiable, which Proposition 3.6 gives on int dom Φ
--   - reading: ⟨T⟩, 'the bit-length of the tensor tuple' (not defined in the paper) → bitLength T = ∑ over entries a + bi of (1 + Nat.size |a|) + (1 + Nat.size |b|); reason: standard binary encoding length; any encoding within a constant factor gives the same polynomial bound
--   - generalization: Ten(n_0; n_1, …, n_d) with d ≥ 1 → any d : ℕ, including d = 0; reason: d = 0 is a degenerate case (trivial group, Δ(T) a point) where the claim holds; at d ≥ 1 the statement is the source's
--   - encoding: poly(d, n_max) and poly(d, n_max, ⟨T⟩) → C(1 + d + n_max)^c and C'(1 + d + n_max + ⟨T⟩)^{c'} with C, c (resp. C', c') existentially quantified before every instance; reason: every polynomial with these arguments is bounded by such an expression and conversely; one polynomial for all instances
--   - encoding: 'Theorem 6.27 holds with the following convergence bound' → under Theorem 6.27's hypotheses except the choice of a minimizer p⋆; reason: the bound does not involve p⋆, and a minimizer always exists (ϕ is l.s.c. and Δ(T) compact, p. 30)
-- source:
--   Doğan, Sakabe, Walter, Convex optimization on moment polytopes, arXiv:2609.06633 (PDF sha256 fcf40771…), p. 44, Theorem 6.28 (proof p. 46)

import Mathlib
import Definitions.Def_MomentPolytopes_QuantumFunctionals_Spectra
import Definitions.Def_MomentPolytopes_QuantumFunctionals_TensorAction
import Definitions.Def_MomentPolytopes_QuantumFunctionals_EntanglementPolytope
import Definitions.Def_MomentPolytopes_QuantumFunctionals_MirrorDescent
import Definitions.Def_MomentPolytopes_QuantumFunctionals_Capacity
import Definitions.Def_MomentPolytopes_QuantumFunctionals_GaussianInteger

set_option autoImplicit false

open scoped ComplexOrder Matrix

namespace MomentPolytopes.QuantumFunctionals

/-- Theorem 6.28 (p. 44). (a) One polynomial `C (1 + d + n_max)^c` bounds `−log Cap_p(T)` for
every nonzero Gaussian-integer tensor tuple `T` of every shape and every `p ∈ Δ(T)`.
(b) Accordingly, one polynomial `C' (1 + d + n_max + ⟨T⟩)^{c'}` gives the convergence bound of
Theorem 6.27: whenever Theorem 6.27's hypotheses hold for a Gaussian-integer `T`,
`ϕ(spec µ(T_k)) − min_{p∈Δ(T)} ϕ(p) ≤ poly(d, n_max, ⟨T⟩)/(ηk)` for all `k ≥ 1`. -/
theorem theorem_6_28 :
    (∃ C : ℝ, ∃ c : ℕ, ∀ (d n0 : ℕ) (n : Fin d → ℕ) (T : Ten d n0 n), T ≠ 0 →
      IsGaussianInteger T → ∀ p ∈ entanglementPolytope T,
        -logCap p T ≤ ((C * (1 + d + nmax n : ℝ) ^ c : ℝ) : EReal)) ∧
    (∃ C : ℝ, ∃ c : ℕ, ∀ (d n0 : ℕ) (n : Fin d → ℕ) (T : Ten d n0 n), T ≠ 0 →
      IsGaussianInteger T → ∀ ϕ : SpecTuple n → EReal, IsAdmissibleObjective ϕ →
      (∀ g : GTuple n, specTuple (momentMap (gact g T)) ∈ interior (effDom ϕ)) →
      ∀ (η : ℝ), 0 < η → ∀ c' : ℕ → ℂ, (∀ k, c' k ≠ 0) →
        StepSizeCondition ϕ η (mirrorDescentSeq ϕ η c' T) c' →
        ∀ k : ℕ, 1 ≤ k →
          ϕ (specTuple (momentMap (mirrorDescentSeq ϕ η c' T k))) -
              ⨅ p ∈ entanglementPolytope T, ϕ p ≤
            ((C * (1 + d + nmax n + bitLength T : ℝ) ^ c / (η * k) : ℝ) : EReal)) := by sorry

end MomentPolytopes.QuantumFunctionals
