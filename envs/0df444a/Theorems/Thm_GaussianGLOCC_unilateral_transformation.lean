-- Prove2me | Theorems.Thm_GaussianGLOCC_unilateral_transformation
-- name    : GaussianGLOCC.unilateral_transformation
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T15:25:19.986556+00:00
-- url     : https://prove2.me/theorems/61d6d50b-171b-4b8d-8e84-c9fa220a7bfd
-- title:
--   Lemma 4: covariance matrix after a unilateral Gaussian operation
-- statement:
--   Let $\rho$ be a Gaussian state of a bipartite system $AB$ with covariance matrix $\gamma=\begin{pmatrix}A&C\\C^T&B\end{pmatrix}$, and let a general Gaussian operation in system $A$ be given by its Choi–Jamiołkowski state $\chi$, a Gaussian state with covariance matrix $\Gamma_A=\begin{pmatrix}\Gamma_{1A}&\Gamma_{12A}\\\Gamma_{12A}^T&\Gamma_{2A}\end{pmatrix}$ (output block first). Then the operation succeeds with positive probability, and the normalized output state is Gaussian with covariance matrix $\gamma'=\begin{pmatrix}A'&C'\\C'^T&B'\end{pmatrix}$, where
--
--   $$
--   \begin{aligned}
--   A'&=\Gamma_{1A}-\tilde\Gamma_{12A}(\tilde\Gamma_{2A}+A)^{-1}\tilde\Gamma_{12A}^T,\\
--   B'&=B-C^T(\tilde\Gamma_{2A}+A)^{-1}C,\\
--   C'&=\tilde\Gamma_{12A}(\tilde\Gamma_{2A}+A)^{-1}C,
--   \end{aligned}
--   $$
--
--   with $\tilde\Gamma_{12A}=\Gamma_{12A}\Lambda$ and $\tilde\Gamma_{2A}=\Lambda\Gamma_{2A}\Lambda$.
--
--   Lemma 4 is the form of a one-party Gaussian operation used in the proof of Theorem 1.
--
--   Differences from the source:
--   - generalization: a Gaussian state of an n × n mode system and an operation from A to A → any numbers nA, nB of modes and any number m of output modes; reason: the formula holds for all mode numbers; nA = nB = n is the paper's case
--   - reading: general Gaussian local operation in system A characterized by a CM Γ_A → contraction with a Gaussian state χ of CM Γ_A, X = Tr_{A_in}[(χ ⊗ 𝟙_B)(ρ^{T_A} ⊗ 𝟙)], normalized by its trace; reason: the state–operation isomorphism the paper uses (pp.3–4, Ref. [13]); with this convention the + sign of (19c) and Λ on the input block of (8) are correct
--   - encoding: the CM γ′ after the operation → conclusions: every series of the contraction converges, the trace is positive, and the normalized output is GaussianWithCovariance with CM unilateralCM Γ_A γ; reason: the convergence and positivity clauses make the normalized output well defined; they hold for Gaussian χ and ρ
-- source:
--   Giedke–Eisert–Cirac–Plenio, Entanglement transformations of pure Gaussian states, arXiv:quant-ph/0301038v1, Lemma 4, eqs. (17)–(19c), p.6; eq. (8), p.4

import Mathlib
import Definitions.Def_GaussianGLOCC_Unilateral
open QAlgorithms.Papers.Independent.Claimed50.P19 (Cov FockIndex DensityKernel GaussianWithCovariance)
open QAlgorithms.Papers.Independent.Claimed50.P37 (successTrace normalizeFockCoefficients)

namespace GaussianGLOCC

/-- Giedke–Eisert–Cirac–Plenio, arXiv:quant-ph/0301038v1, Lemma 4 (Unilateral transformations),
p.6: "Let γ be a CM of a Gaussian state of an n × n mode system consisting of systems A and B,
partitioned as γ = [[A, C], [Cᵀ, B]]. (17) The CM γ′ after application of a general Gaussian
local operation in system A characterized by a CM Γ_A = [[Γ₁A, Γ₁₂A], [Γ₁₂Aᵀ, Γ₂A]] (18) is given
by a matrix of the form as in Eq. (17) with A′ = Γ₁A − Γ̃₁₂A(Γ̃₂A + A)⁻¹Γ̃₁₂Aᵀ, (19a)
B′ = B − Cᵀ(Γ̃₂A + A)⁻¹C, (19b) C′ = Γ̃₁₂A(Γ̃₂A + A)⁻¹C. (19c)"

Let `ρ` be a Gaussian state (any first moments) of `nA + nB` modes with CM `γ`, and let `χ` be a
Gaussian state of `m + nA` modes (output modes first) with CM `Γ_A`, the Choi–Jamiołkowski state
of a Gaussian operation in A. Then every series in the contraction
`X = Tr_{A_in}[(χ ⊗ 𝟙_B)(ρ^{T_A} ⊗ 𝟙)]` converges, its trace is positive, and the normalized
output `X / tr X` is a Gaussian state with CM `[[A′, C′], [C′ᵀ, B′]]` given by (19a)–(19c).

**Formalization Note.** The operation "characterized by a CM Γ_A" is the contraction with a
Gaussian state `χ` of CM `Γ_A` (the state–operation isomorphism of pp.3–4, Ref. [13]); its output
is normalized (`successTrace`, `normalizeFockCoefficients` of the published
`Claimed50.P37`). The tilde is `Γ̃ = (𝟙 ⊕ Λ)Γ(𝟙 ⊕ Λ)` (eq. (8)), `𝟙` on the output block.
The mode numbers `m`, `nA`, `nB` are arbitrary (the paper's `n × n` is `nA = nB = n`). -/
theorem unilateral_transformation {m nA nB : ℕ} (ρ : DensityKernel (nA + nB)) (γ : Cov (nA + nB))
    (χ : DensityKernel (m + nA)) (ΓA : Cov (m + nA))
    (hρ : GaussianWithCovariance ρ γ) (hχ : GaussianWithCovariance χ ΓA) :
    (∀ (a b : FockIndex (m + nB)) (i : FockIndex nA), Summable (fun j : FockIndex nA =>
      χ (joinAB (splitA a) i) (joinAB (splitA b) j) * ρ (joinAB i (splitB a)) (joinAB j (splitB b)))) ∧
    (∀ a b : FockIndex (m + nB), Summable (fun i : FockIndex nA => ∑' j : FockIndex nA,
      χ (joinAB (splitA a) i) (joinAB (splitA b) j) * ρ (joinAB i (splitB a)) (joinAB j (splitB b)))) ∧
    0 < successTrace (localContractionA χ ρ) ∧
    GaussianWithCovariance (normalizeFockCoefficients (localContractionA χ ρ))
      (unilateralCM ΓA γ) := by sorry

end GaussianGLOCC
