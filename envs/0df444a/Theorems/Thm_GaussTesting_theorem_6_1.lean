-- Prove2me | Theorems.Thm_GaussTesting_theorem_6_1
-- name    : GaussTesting.theorem_6_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T17:02:13.642194+00:00
-- url     : https://prove2.me/theorems/e41ab229-5f3a-4a18-bd82-4b0c62d6c149
-- title:
--   Theorem 6.1 — a size-independent tester for bosonic Gaussian states ($\beta=\sqrt{405/2}$, three copies per round)
-- statement:
--   Let $\beta=\sqrt{405/2}$. There is a constant $A>0$ such that for every number of modes $n$, all $0\le\varepsilon_1<\varepsilon_2<1$ with $\varepsilon_2>\beta\varepsilon_1$ and all $0<\delta\le1/2$, there is an $(\varepsilon_1,\varepsilon_2,\delta)$-tester for the class $G_b$ of bosonic Gaussian states that acts on three copies at a time and uses
--
--   $$
--   t\ \le\ A\,\frac{\log(1/\delta)}{(\varepsilon_2-\beta\varepsilon_1)^2}
--   $$
--
--   copies in total. The tester must be correct for every pure state of the full $n$-mode Fock space.
--
--   This is the clause of Theorem 1.4 for bosonic Gaussian states, with the explicit constant $\beta$ that the proof produces.
--
--   Differences from the source:
--   - reading: a t-copy (ε₁, ε₂, δ)-tester acting on k copies of the state at a time → a BlockTester: one two-outcome measurement {E, I − E} on ℋ^{⊗k} repeated in independent rounds, a deterministic decision on the outcomes, t = k · rounds; reason: this makes 'acting on k copies at a time' precise (Table 1, Algorithm 1); every such procedure is a tester in the sense of Definition 1.2
--   - reading: an O(log(1/δ)/(ε₂ − βε₁)²)-copy tester → one constant A > 0, chosen before the number of modes n and before δ, ε₁, ε₂, with t ≤ A · log(1/δ)/(ε₂ − βε₁)²; reason: the bound is size independent (p.5: independent of n and of any energy bound)
--   - encoding: the fermionic Fock space ⋀ℂⁿ and the bosonic Fock space ⋁ℂⁿ → ℓ²(Fin n → Fin 2) (Jordan–Wigner, 1 = occupied, 0-based modes) and ℓ²(Fin n → ℕ); ℋ^{⊗k} is ℓ²(Fin k → ι); reason: unitarily the same spaces; Lean convention
--   - encoding: classes of pure states (rays) → sets of unit vectors closed under global phase (Coh_n gets an explicit e^{iθ}, G_f an explicit phase in its orbit); reason: dist(ψ, 𝒞) is phase-invariant, so no distance changes
--   - reading: G_b (resp. G_{b,0}) = the orbit of |0ⁿ⟩ under (zero-mean) bosonic Gaussian unitaries → unit vectors annihilated, coefficientwise, by the transformed annihilators (r_j + i r_{n+j}) + Σ_k (S_{jk} + i S_{n+j,k}) v_k for some S ∈ Sp(2n, ℝ) and r ∈ ℝ²ⁿ (r = 0 for G_{b,0}); reason: ψ = U|0ⁿ⟩ iff U a_j U† ψ = 0 for all j; the equations determine ψ up to scale; Mathlib has no metaplectic representation on ℓ²(ℕⁿ)
-- source:
--   Iyer, O'Gorman, Parekh, Thompson, Zhao, Optimal testing of fermionic and bosonic Gaussian states, arXiv:2609.39113 (sha256 6683e57b…), Theorem 6.1, p.55

import Definitions.Def_GaussTesting_Gb
import Definitions.Def_GaussTesting_IsTester

namespace GaussTesting

/-- **Theorem 6.1.** Let `β = √(405/2)`. For all `0 ≤ ε₁ < ε₂ < 1` with `ε₂ > βε₁` and `0 < δ ≤ 1/2`, there is an
`O(log(1/δ)/(ε₂−βε₁)²)`-copy `(ε₁, ε₂, δ)`-tester for bosonic Gaussian states. The tester acts on three copies at a time.

Source: Iyer, O'Gorman, Parekh, Thompson, Zhao, *Optimal testing of fermionic and bosonic Gaussian states*, arXiv:2609.39113 (sha256 6683e57b…), Theorem 6.1, p.55. The range `δ ≤ 1/2` is the printed one (it contains Theorem 1.4's `δ < 1/2`).

**Formalization Note.** "There is an `O(log(1/δ)/(ε₂−βε₁)²)`-copy tester" is pinned as: one constant
`A > 0`, chosen before the number of modes `n` and before `δ, ε₁, ε₂`, such that the tester uses
`t = k · rounds ≤ A · log(1/δ)/(ε₂ − βε₁)²` copies (size independence, Theorem 1.4, p.5). The tester
measures blocks of `k` copies (`BlockTester _ k`) and must work for every unit vector of the full Fock
space. -/
theorem theorem_6_1 :
    ∃ A : ℝ, 0 < A ∧ ∀ (n : ℕ) (δ ε₁ ε₂ : ℝ), 0 ≤ ε₁ → ε₁ < ε₂ → ε₂ < 1 → Real.sqrt (405 / 2) * ε₁ < ε₂ →
      0 < δ → δ ≤ 1 / 2 →
      ∃ T : BlockTester (Fin n → ℕ) 3, IsTester (Gb n) T ε₁ ε₂ δ ∧
        ((3 * T.rounds : ℕ) : ℝ) ≤ A * (Real.log (1 / δ) / (ε₂ - Real.sqrt (405 / 2) * ε₁) ^ 2) := by sorry

end GaussTesting
