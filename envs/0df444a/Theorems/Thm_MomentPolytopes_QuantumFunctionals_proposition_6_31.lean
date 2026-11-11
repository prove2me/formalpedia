-- Prove2me | Theorems.Thm_MomentPolytopes_QuantumFunctionals_proposition_6_31
-- name    : MomentPolytopes.QuantumFunctionals.proposition_6_31
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T01:04:59.429259+00:00
-- url     : https://prove2.me/theorems/fe2268a5-2c1a-449f-8efd-00f6eac0b796
-- title:
--   Proposition 6.31 — a random integer tuple with entries in [S], log S ≤ poly(d, n_max), certifies Δ(T) = {p ∈ C | log cap_p(g·T) > −∞} with probability ≥ 1/2
-- statement:
--   There is one polynomial bound $C(1+d+n_{\max})^c$ with the following property. For every $d$ and $n_{\max}$ there is an integer $S\ge1$ with $\log S\le C(1+d+n_{\max})^c$ such that: for all $n_1,\dots,n_d$ with $\max_\ell n_\ell=n_{\max}$, every $n_0$ and every $0\ne T\in\mathrm{Ten}(n_0;n_1,\dots,n_d)$, if $g=(g_1,\dots,g_d)$ is a random tuple of integer matrices whose entries are drawn independently and uniformly from $[S]=\{1,\dots,S\}$, then with probability at least $1/2$
--   $$g\in\mathrm{GL}(n_1)\times\dots\times\mathrm{GL}(n_d)\quad\text{and}\quad\Delta(T)=\{p\in C\mid\log\operatorname{cap}_p(g\cdot T)>-\infty\}.$$
--
--   The paper cites this from [vdBCL+25a, Thm. 3.6] (fn. 33 explains the generalization to $n_0\ge1$, all $d$, and full matrices). It supplies the generic integer group element in the proof of Theorem 6.28.
--
--   Differences from the source:
--   - encoding: ℓ ∈ [d] = {1, …, d} → ℓ : Fin d (0-based); reason: indexing convention; same instances
--   - encoding: log Cap and log cap in [−∞, ∞) → EReal, −∞ = ⊥; the bound is an EReal inequality; reason: Lean convention; same values, no junk value for −∞
--   - generalization: Ten(n_0; n_1, …, n_d) with d ≥ 1 → any d : ℕ, including d = 0; reason: d = 0 is a degenerate case (trivial group, Δ(T) a point) where the claim holds; at d ≥ 1 the statement is the source's
--   - reading: 'There exists an integer S ≥ 1 such that log S ≤ poly(d, n_max) with the following property: Let 0 ≠ T ∈ Ten(n_0; n_1, …, n_d) …' → ∃ C c, ∀ d N, ∃ S ≥ 1, log S ≤ C(1 + d + N)^c ∧ ∀ n with max_ℓ n_ℓ = N, ∀ n_0, ∀ T ≠ 0, …; reason: the shape (n_0; n_1, …, n_d) is introduced after S and the bound on S depends only on (d, n_max); the polynomial is fixed before every instance
--   - encoding: entries drawn independently uniformly from [S]; probability at least 1/2 → g ranges over (ℓ : Fin d) → Fin (n ℓ) → Fin (n ℓ) → Fin S with entry j ↦ j + 1; S^{∑ n_ℓ²} ≤ 2 · #{good g}; reason: the uniform product measure on [S]^{∑ n_ℓ²} is normalized counting
--   - encoding: C (Weyl chamber) → weylChamber = {p | each p ℓ antitone}; reason: C ≅ ℝ^{n_1}_↓ × ⋯ × ℝ^{n_d}_↓ (Example 2.1)
-- source:
--   Doğan, Sakabe, Walter, Convex optimization on moment polytopes, arXiv:2609.06633 (PDF sha256 fcf40771…), p. 45, Proposition 6.31 (cited from [vdBCL+25a, Thm. 3.6])

import Mathlib
import Definitions.Def_MomentPolytopes_QuantumFunctionals_TensorAction
import Definitions.Def_MomentPolytopes_QuantumFunctionals_EntanglementPolytope
import Definitions.Def_MomentPolytopes_QuantumFunctionals_Capacity
import Definitions.Def_MomentPolytopes_QuantumFunctionals_GaussianInteger

set_option autoImplicit false

open scoped ComplexOrder Matrix

namespace MomentPolytopes.QuantumFunctionals

/-- Proposition 6.31 (p. 45, cited from [vdBCL+25a, Thm. 3.6]). There is one polynomial bound
`C (1 + d + n_max)^c` such that for every `d` and `n_max` some integer `S ≥ 1` with
`log S ≤ C (1 + d + n_max)^c` has the property: for every shape `n` with `max_ℓ n_ℓ = n_max`,
every `n_0` and every `0 ≠ T`, a uniformly random tuple `g` of integer matrices with entries in
`[S] = {1, …, S}` (entry `j ∈ Fin S` encodes the integer `j + 1`) satisfies, with probability at
least `1/2`, `g ∈ GL(n_1) × ⋯ × GL(n_d)` and `Δ(T) = {p ∈ C | log cap_p(g · T) > −∞}`.
The probability is the uniform counting measure on the `S^{∑ n_ℓ²}` tuples. -/
theorem proposition_6_31 :
    ∃ C : ℝ, ∃ c : ℕ, ∀ d N : ℕ, ∃ S : ℕ, 1 ≤ S ∧
      Real.log S ≤ C * (1 + d + N : ℝ) ^ c ∧
      ∀ (n : Fin d → ℕ), nmax n = N → ∀ (n0 : ℕ) (T : Ten d n0 n), T ≠ 0 →
        (S ^ (∑ ℓ, n ℓ ^ 2) : ℝ) ≤ 2 * (Nat.card
          {g : (ℓ : Fin d) → Fin (n ℓ) → Fin (n ℓ) → Fin S //
            (∀ ℓ, (Matrix.of fun i j => ((((g ℓ i j : ℕ) + 1 : ℕ) : ℂ))).det ≠ 0) ∧
            entanglementPolytope T =
              {p | p ∈ weylChamber ∧ ⊥ < logCapX (diagTuple p)
                (act (fun ℓ => Matrix.of fun i j => ((((g ℓ i j : ℕ) + 1 : ℕ) : ℂ))) T)}} : ℝ) := by sorry

end MomentPolytopes.QuantumFunctionals
