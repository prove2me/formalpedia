-- Prove2me | Theorems.Thm_GaussTesting_theorem_3_6
-- name    : GaussTesting.theorem_3_6
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T17:02:10.176131+00:00
-- url     : https://prove2.me/theorems/ec1e5ca3-f5e7-4776-bd94-53688b7de74c
-- title:
--   Theorem 3.6 — Algorithm 1 is a $kt$-copy tolerant tester with $t=O(\log(1/\delta)/(\alpha_2(\varepsilon_2-\beta\varepsilon_1)^2))$
-- statement:
--   Let $\mathcal C\subset\mathcal H$ be a nonempty class of pure states. Suppose a base property tester on $k$ copies, with accepting effect $E$ and rejection probability $q(\psi)=1-\langle\psi^{\otimes k}|E|\psi^{\otimes k}\rangle$, satisfies for all pure states $\psi$
--
--   $$
--   \alpha_2\,\mathrm{dist}(\psi,\mathcal C)^2\le q(\psi)\le\alpha_1\,\mathrm{dist}(\psi,\mathcal C)^2\qquad(3.46)
--   $$
--
--   with $\alpha_1\ge1$ and $0<\alpha_2\le1/2$. Let $\beta=\sqrt{\alpha_1/\alpha_2}$. Then there is an absolute constant $A>0$ such that for all $0<\delta<1/2$ and $0\le\varepsilon_1<\varepsilon_2\le1$ with $\varepsilon_2>\beta\varepsilon_1$, and every number of rounds
--
--   $$
--   t\ \ge\ A\,\frac{\log(1/\delta)}{\alpha_2(\varepsilon_2-\beta\varepsilon_1)^2},
--   $$
--
--   Algorithm 1 (with this base tester, $t$ rounds and threshold $\theta(\alpha_1\varepsilon_1^2,\alpha_2\varepsilon_2^2)$) is a $kt$-copy $(\varepsilon_1,\varepsilon_2,\delta)$-tester for $\mathcal C$.
--
--   Together with Theorem 3.5, this reduces each class of the paper to a spectral-gap computation.
--
--   Differences from the source:
--   - reading: a base property tester 𝒜 on k copies with rejection probability q(ψ) → an effect E on ℋ^{⊗k} (0 ≤ E ≤ I) with q(ψ) = 1 − ⟨ψ^{⊗k}|E|ψ^{⊗k}⟩; reason: the most general two-outcome measurement on k copies
--   - reading: t = O(log(1/δ)/(α₂(ε₂ − βε₁)²)) → ∃ absolute A > 0 (independent of ℋ, k, E, 𝒞, α₁, α₂, δ, ε₁, ε₂) such that Algorithm 1 is correct for every t ≥ A · log(1/δ)/(α₂(ε₂ − βε₁)²); reason: the proof applies Lemma 2.14, whose constant is absolute
--   - reading: the ranges of δ, ε₁, ε₂ (not repeated in the theorem) → 0 < δ < 1/2 and 0 ≤ ε₁ < ε₂ ≤ 1; reason: these are Algorithm 1's input conditions (p.28) and Definition 1.2's
--   - encoding: a Hilbert space ℋ → ℓ²(ι) for an arbitrary index type ι; reason: every Hilbert space is isometric to some ℓ²(ι)
--   - encoding: a class 𝒞 of pure states; pure states |ψ⟩ ∈ ℋ → a set C of unit vectors (∀ φ ∈ C, ‖φ‖ = 1); unit vectors ψ; reason: a pure state is a unit vector of ℋ
-- source:
--   Iyer, O'Gorman, Parekh, Thompson, Zhao, Optimal testing of fermionic and bosonic Gaussian states, arXiv:2609.39113 (sha256 6683e57b…), Theorem 3.6, eq. (3.46), p.27; Algorithm 1, p.28

import Definitions.Def_GaussTesting_algorithm1
import Definitions.Def_GaussTesting_IsTester

namespace GaussTesting

/-- **Theorem 3.6 (Tolerant testing sample complexity).** Let `𝒞 ⊂ ℋ` be nonempty. Suppose the rejection
probability `q(ψ) = 1 − ⟨ψ^{⊗k}|E|ψ^{⊗k}⟩` of a base property tester on `k` copies (accepting effect `E`)
satisfies `α₂ dist(ψ, 𝒞)² ≤ q(ψ) ≤ α₁ dist(ψ, 𝒞)²` for all pure states (3.46), with `α₁ ≥ 1` and
`0 < α₂ ≤ 1/2`. Then Algorithm 1 is a `kt`-copy `(ε₁, ε₂, δ)`-tester for `𝒞` provided `ε₂ > βε₁` with
`β = √(α₁/α₂)` and `t = O(log(1/δ)/(α₂(ε₂ − βε₁)²))`.

Source: Iyer, O'Gorman, Parekh, Thompson, Zhao, *Optimal testing of fermionic and bosonic Gaussian states*, arXiv:2609.39113 (sha256 6683e57b…), Theorem 3.6, eq. (3.46), p.27; Algorithm 1, p.28.

**Formalization Note.** "`t = O(·)`" is pinned as one absolute constant `A` (independent of `ι, k, E, 𝒞,
α₁, α₂, δ, ε₁, ε₂`) such that Algorithm 1 is correct for every `t ≥ A·log(1/δ)/(α₂(ε₂ − βε₁)²)`. The
ranges `0 < δ < 1/2` and `0 ≤ ε₁ < ε₂ ≤ 1` are the input conditions of Algorithm 1 (p.28). Algorithm 1
with `t` rounds uses `k·t` copies by construction. -/
theorem theorem_3_6 :
    ∃ A : ℝ, 0 < A ∧ ∀ {ι : Type*} {k : ℕ} (C : Set (Ell2 ι))
      (E : Ell2 (Fin k → ι) →L[ℂ] Ell2 (Fin k → ι)) (hE₀ : E.IsPositive) (hE₁ : (1 - E).IsPositive)
      (α₁ α₂ : ℝ), C.Nonempty → (∀ φ ∈ C, ‖φ‖ = 1) → 1 ≤ α₁ → 0 < α₂ → α₂ ≤ 1 / 2 →
      (∀ ψ : Ell2 ι, ‖ψ‖ = 1 →
        α₂ * distTo ψ C ^ 2 ≤ 1 - (inner ℂ (tpow k ψ) (E (tpow k ψ))).re ∧
          1 - (inner ℂ (tpow k ψ) (E (tpow k ψ))).re ≤ α₁ * distTo ψ C ^ 2) →
      ∀ (δ ε₁ ε₂ : ℝ), 0 < δ → δ < 1 / 2 → 0 ≤ ε₁ → ε₁ < ε₂ → ε₂ ≤ 1 →
        Real.sqrt (α₁ / α₂) * ε₁ < ε₂ →
        ∀ t : ℕ, A * Real.log (1 / δ) / (α₂ * (ε₂ - Real.sqrt (α₁ / α₂) * ε₁) ^ 2) ≤ t →
          IsTester C (algorithm1 E hE₀ hE₁ t ε₁ ε₂ α₁ α₂) ε₁ ε₂ δ := by sorry

end GaussTesting
