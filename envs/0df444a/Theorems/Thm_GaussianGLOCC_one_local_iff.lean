-- Prove2me | Theorems.Thm_GaussianGLOCC_one_local_iff
-- name    : GaussianGLOCC.one_local_iff
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T15:24:52.52143+00:00
-- url     : https://prove2.me/theorems/882a6145-7646-4e56-abb6-73aecc41fcd3
-- title:
--   Lemma 3: one-local operations are sufficient
-- statement:
--   Let $\rho$, $\rho'$ be pure Gaussian states of $n\times n$ modes with covariance matrices $\gamma$, $\gamma'$. Then $\rho$ can be transformed into $\rho'$ by Gaussian local operations with classical communication (GLOCC) if and only if $\rho$ can be transformed into $\rho'$ by **one-local** Gaussian operations: Gaussian local operations in system $A$ with communication from $A$ to $B$ only, together with local Gaussian unitary operations in $B$.
--
--   Transformations are deterministic: every measurement outcome must lead to $\rho'$.
--
--   Differences from the source:
--   - reading: transformed under GLOCC / by one-local Gaussian operations → GLOCCReach / OneLocalReach: deterministic adaptive protocols of local Gaussian unitaries, vacuum ancillas, discarding and X-homodyne detections (B restricted to unitaries in OneLocalReach); reason: the paper's description of Gaussian operations (pp.2–3: optical elements together with homodyne measurements, on possibly a larger set of modes) and the parenthetical of Lemma 3; a homodyne step needs a continuation for every outcome y ∈ ℝ, which for Gaussian protocols is the same as for almost every y, since conditional states for different y differ by local displacements (those of B use the communicated y)
--   - encoding: pure Gaussian state of n × n modes with CM γ (eqs. (1)–(2), vacuum CM 𝟙) → IsPureGaussian ρ γ on DensityKernel (n + n), A = first n modes, B = last n modes (published GaussianWithCovariance plus a norm-one vector representative); reason: the published predicate's extra clauses (γ positive definite, finite mean energy) hold for every Gaussian state; the mode order is a layout choice
-- source:
--   Giedke–Eisert–Cirac–Plenio, Entanglement transformations of pure Gaussian states, arXiv:quant-ph/0301038v1, Lemma 3, p.5

import Mathlib
import Definitions.Def_GaussianGLOCC_SqueezedStates
import Definitions.Def_GaussianGLOCC_GLOCCReach
open QAlgorithms.Papers.Independent.Claimed50.P19 (Cov FockIndex DensityKernel GaussianWithCovariance)

namespace GaussianGLOCC

/-- Giedke–Eisert–Cirac–Plenio, arXiv:quant-ph/0301038v1, Lemma 3 (One-local operations are
sufficient), p.5: "Given two n × n pure states ρ and ρ′ with CM γ and γ′, respectively. Then ρ
can be transformed into ρ′ under GLOCC, iff ρ can be transformed into ρ′ by one-local Gaussian
operations (i.e., Gaussian local operations in system A with communication from system A to B
only together with local Gaussian unitary operations in B)."

**Formalization Note.** GLOCC is the deterministic, adaptive protocol relation `GLOCCReach`
(see its docstring for the reading of pp.2–3); one-local operations are `OneLocalReach`
(B restricted to local Gaussian unitaries, which may depend on A's outcomes). Both directions
of the iff are stated. -/
theorem one_local_iff (n : ℕ) (ρ ρ' : DensityKernel (n + n)) (γ γ' : Cov (n + n))
    (hρ : IsPureGaussian ρ γ) (hρ' : IsPureGaussian ρ' γ') :
    GLOCCReach ⟨n, n, ρ⟩ ⟨n, n, ρ'⟩ ↔ OneLocalReach ⟨n, n, ρ⟩ ⟨n, n, ρ'⟩ := by sorry

end GaussianGLOCC
