-- Prove2me | Theorems.Thm_GuanQinQDP_Restricted_reachability_from_pure
-- name    : GuanQinQDP.Restricted.reachability_from_pure
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-11T03:42:35.868649+00:00
-- url     : https://prove2.me/theorems/11b40272-9a0a-41da-b476-ae80c462db3d
-- title:
--   Lemma 3.4 — equal marginals with a pure source imply local reachability
-- statement:
--   Let $H_i$ and $R$ be finite-dimensional, and let $\rho,\sigma$ be states on $H_i\otimes R$. Suppose $\rho$ is pure and $\operatorname{Tr}_i\rho=\operatorname{Tr}_i\sigma$. Then
--
--   $$\sigma=(\Phi\otimes\mathrm{id}_R)(\rho)$$
--
--   for some channel $\Phi$ on register $i$. The target $\sigma$ may be mixed, and $\rho$ need not have full Schmidt rank.
--
--   This is the third reduction of §3.2. A pure member turns the necessary condition of equal marginals into the neighbor relation of Definition 2.1.
--
--   Differences from the source:
--
--   - encoding: ρ pure → ρ = |ψ⟩⟨ψ| (pureDensity ψ) for a vector ψ, together with IsDensityMatrix ρ; reason: trace one forces ‖ψ‖ = 1; this is the rank-one pure state
-- source:
--   Ji Guan, Yecheng Qin, Parallel Composition of Quantum Differential Privacy: The Role of Measurement Restrictions, STOC 2027 submission #1640 (October 2026), source.pdf SHA-256 da23c8347251683a16df4c61de3fa1604211cdbf34d757a7a45feb0efd54c694, Lemma 3.4 (printed p. 17 / PDF p. 18)

import Definitions.Def_GuanQinQDP_Restricted_Model
open QAlgorithms WildeQIT.EntBreaking

namespace GuanQinQDP.Restricted

/-- Lemma 3.4 (Reachability from a pure state), Guan–Qin, STOC 2027 submission #1640, printed
p. 17 / PDF p. 18. Let `H_i` and `R` be finite-dimensional, and let `ρ, σ` be states on
`H_i ⊗ R` with `ρ` pure and `Tr_i ρ = Tr_i σ`. Then `σ = (Φ ⊗ id_R)(ρ)` for some channel `Φ` on
register `i` (`σ` may be mixed). -/
theorem reachability_from_pure {I R : Type} [Fintype I] [DecidableEq I] [Fintype R]
    (ρ σ : Matrix (I × R) (I × R) ℂ) (hρ : IsDensityMatrix ρ) (hσ : IsDensityMatrix σ)
    (hpure : ∃ ψ : EuclideanSpace ℂ (I × R), ρ = pureDensity ψ)
    (hmarg : traceLeft ρ = traceLeft σ) :
    ∃ Φ : Matrix I I ℂ →ₗ[ℂ] Matrix I I ℂ, IsQuantumChannel Φ ∧ σ = applyFirst Φ ρ := by sorry

end GuanQinQDP.Restricted
