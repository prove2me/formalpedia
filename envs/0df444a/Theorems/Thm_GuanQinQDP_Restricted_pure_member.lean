-- Prove2me | Theorems.Thm_GuanQinQDP_Restricted_pure_member
-- name    : GuanQinQDP.Restricted.pure_member
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-11T03:42:39.462216+00:00
-- url     : https://prove2.me/theorems/f999d4bf-2d63-4736-a68d-8381d34627bf
-- title:
--   Lemma 3.3 — an optimal pair of $L_{\gamma,i}(B)$ with a pure member when $\dim R\le2$
-- statement:
--   Let $R$ be a finite-dimensional space with $\dim R\le2$, let $\gamma\ge1$, and let $B$ be a Hermitian operator on $\mathbb C^2\otimes R$. Then the equal-marginal program
--
--   $$L_{\gamma,i}(B)=\max\big\{\operatorname{Tr}[B(\rho-\gamma\sigma)] : \rho,\sigma\in D(\mathbb C^2\otimes R),\ \operatorname{Tr}_i\rho=\operatorname{Tr}_i\sigma\big\}$$
--
--   has an optimal pair $(\rho,\sigma)$ in which $\rho$ or $\sigma$ is pure. That is, $\rho=|\psi\rangle\langle\psi|$ or $\sigma=|\psi\rangle\langle\psi|$ for some vector $\psi$. The lemma does not claim that both are pure.
--
--   This is the second reduction of §3.2. Combined with Lemma 3.4, it makes the equal-marginal relaxation exact on compressed spaces.
--
--   Differences from the source:
--
--   - encoding: an optimal pair of the program L_{γ,i}(B) → a feasible pair whose value pairValue B ρ σ γ is ≥ that of every feasible pair; reason: this is the meaning of optimal; it also asserts attainment, as the source does
--   - encoding: R a (nonzero) finite-dimensional space with dim R ≤ 2 → [Nonempty R], Fintype.card R ≤ 2; reason: excludes only the zero space, on which there are no states
--   - encoding: Tr[B(ρ − γσ)] → pairValue B ρ σ γ, the real part of the trace; reason: B and ρ − γσ are Hermitian, so the trace is real
-- source:
--   Ji Guan, Yecheng Qin, Parallel Composition of Quantum Differential Privacy: The Role of Measurement Restrictions, STOC 2027 submission #1640 (October 2026), source.pdf SHA-256 da23c8347251683a16df4c61de3fa1604211cdbf34d757a7a45feb0efd54c694, Lemma 3.3 (printed p. 17 / PDF p. 18), with the standing assumptions of §3 (printed p. 15 / PDF p. 16)

import Definitions.Def_GuanQinQDP_Restricted_Model
open QAlgorithms
open scoped Matrix

namespace GuanQinQDP.Restricted

/-- Lemma 3.3 (Pure member), Guan–Qin, STOC 2027 submission #1640, printed p. 17 / PDF p. 18.
If `dim R ≤ 2`, then for every `γ ≥ 1` and every Hermitian `B` on `ℂ² ⊗ R` the program
`L_{γ,i}(B)` has an optimal pair in which `ρ` or `σ` is pure: there are density operators `ρ, σ`
with `Tr_i ρ = Tr_i σ`, one of them of the form `|ψ⟩⟨ψ|`, whose value `Tr[B(ρ − γσ)]` is at least
the value of every feasible pair. -/
theorem pure_member {R : Type} [Fintype R] [DecidableEq R] [Nonempty R]
    (hR : Fintype.card R ≤ 2) (γ : ℝ) (hγ : 1 ≤ γ)
    (B : Matrix (Qubit × R) (Qubit × R) ℂ) (hB : B.IsHermitian) :
    ∃ ρ σ : Matrix (Qubit × R) (Qubit × R) ℂ,
      IsDensityMatrix ρ ∧ IsDensityMatrix σ ∧ traceLeft ρ = traceLeft σ ∧
      ((∃ ψ : EuclideanSpace ℂ (Qubit × R), ρ = pureDensity ψ) ∨
        (∃ ψ : EuclideanSpace ℂ (Qubit × R), σ = pureDensity ψ)) ∧
      ∀ ρ' σ' : Matrix (Qubit × R) (Qubit × R) ℂ,
        IsDensityMatrix ρ' → IsDensityMatrix σ' → traceLeft ρ' = traceLeft σ' →
          pairValue B ρ' σ' γ ≤ pairValue B ρ σ γ := by sorry

end GuanQinQDP.Restricted
