-- Prove2me | Theorems.Thm_GaussianGLOCC_tmss_degrade_one_local
-- name    : GaussianGLOCC.tmss_degrade_one_local
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T15:25:51.535815+00:00
-- url     : https://prove2.me/theorems/b10bd5a8-e9da-4387-b413-5bc1042a765e
-- title:
--   p.7: two-step physical realization of the TMSS degradation by one-local Gaussian operations (corrected: B applies a fixed Gaussian unitary besides the displacement)
-- statement:
--   Let $0\le r'<r$ and let $|\psi_r\rangle$ be the two-mode squeezed state with parameter $r$, mode $A$ held by $A$ and mode $B$ by $B$. There are
--
--   1. a Gaussian unitary $U$ on $A$'s mode together with an additional vacuum mode appended to $A$,
--   2. for every outcome $y\in\mathbb R$ of an ideal homodyne detection of the additional mode, a conditional state $\sigma_y$ of the remaining two modes, and
--   3. an outcome-dependent phase-space displacement $D_A(y)$ on $A$ and outcome-dependent local Gaussian unitaries $D_B(y)$ on $B$ whose symplectic part does not depend on $y$ (a fixed Gaussian unitary of $B$ followed by the communicated displacement),
--
--   such that $(D_A(y)\otimes D_B(y))\,\sigma_y\,(D_A(y)\otimes D_B(y))^\dagger=|\psi_{r'}\rangle\langle\psi_{r'}|$ for **every** outcome $y$. In particular $|\psi_r\rangle\langle\psi_r|$ can be transformed deterministically into $|\psi_{r'}\rangle\langle\psi_{r'}|$ by one-local Gaussian operations.
--
--   Only the displacement in $B$ needs the communicated outcome.
--
--   **Correction.** The page says that only a displacement is needed in $B$. With one real homodyne outcome this is false for every $0\le r'<r$: $B$'s conditional states average to $B$'s marginal, with covariance matrix $\cosh(r)\mathbb 1$; if each had covariance matrix $\cosh(r')\mathbb 1$, their means $m(y)$, which are affine in the scalar outcome $y$, would need covariance $(\cosh r-\cosh r')\mathbb 1$ of rank 2, while an affine image of a scalar has covariance of rank at most 1. So $B$ must also apply a fixed (outcome-independent) Gaussian unitary.
--
--   Differences from the source:
--   - correction: no action is needed in system B (second moments); the outcome is communicated only to apply a local displacement in B → DB y is a Gaussian unitary of B whose symplectic matrix is the same for every y (a fixed unitary followed by an outcome-dependent displacement); reason: the printed claim is false for every 0 ≤ r′ < r — B's conditional CMs cosh(r′)𝟙 would have to add up, with the rank-≤1 covariance of means affine in one real outcome y, to B's marginal CM cosh(r)𝟙, which needs rank 2
--   - reading: an appropriate Gaussian unitary on the single mode of A and an additional vacuum field mode, a homodyne detection in the additional mode, a local displacement → ∃ U on A's two modes after appendVacuumA, conditional states σ y of HomodyneLastA (X quadrature) for every y, a displacement (symplectic matrix 𝟙) DA y on A, result tmssProduct ![r′]; plus OneLocalReach; reason: X-homodyne is no restriction (a phase shift in U selects the quadrature); A's own displacement is a local step needing no communication, and A's fixed symplectic correction commutes with the ancilla measurement and is absorbed into U
-- source:
--   Giedke–Eisert–Cirac–Plenio, Entanglement transformations of pure Gaussian states, arXiv:quant-ph/0301038v1, p.7, first paragraph

import Mathlib
import Definitions.Def_GaussianGLOCC_SqueezedStates
import Definitions.Def_GaussianGLOCC_GLOCCReach
open QAlgorithms.Papers.Independent.Claimed50.P19 (DensityKernel)
open QAlgorithms.Papers.Independent.Renew46.P39 (AffineMultimodeGaussianUnitary)

namespace GaussianGLOCC

/-- Giedke–Eisert–Cirac–Plenio, arXiv:quant-ph/0301038v1, p.7, first paragraph: "Physically,
this operation can be implemented in two steps: first, one implements an appropriate Gaussian
unitary operation on both the single mode of system A and an additional vacuum field mode. […]
Then, in a second step, one realizes a homodyne detection in the additional field mode. […] the
classical outcome needs to be communicated only to apply the appropriate local displacement in
phase space in system B."

For `0 ≤ r′ < r` (A = mode 0, B = mode 1 of the TMSS `|ψ_r⟩`), there are
1. a Gaussian unitary `U` on A's mode together with an additional vacuum mode appended to A,
2. for every outcome `y ∈ ℝ` of the ideal homodyne detection of that additional mode, the
   conditional state `σ y` of the remaining two modes, and
3. outcome-dependent phase-space displacements `D_A y` on A (symplectic matrix `𝟙`) and local
   Gaussian unitaries `D_B y` on B whose symplectic matrix does not depend on `y` (a fixed
   Gaussian unitary of B followed by the communicated displacement),

such that `(D_A y ⊗ D_B y) (σ y) (D_A y ⊗ D_B y)† = |ψ_{r′}⟩⟨ψ_{r′}|` for **every** `y`; and
consequently `|ψ_r⟩⟨ψ_r|` can be transformed deterministically into `|ψ_{r′}⟩⟨ψ_{r′}|` by one-local
Gaussian operations.

**Formalization Note.** The homodyne detection measures the X quadrature (`HomodyneLastA`); a
phase shift inside `U` selects any other quadrature. A's own displacement is a local step that
needs no communication.

**Correction.** The page says that B needs only a displacement ("no action is needed in system
B" on second moments). With a single real homodyne outcome this is false for every
`0 ≤ r′ < r`: whatever A does, B's conditional states average to B's marginal, whose CM is
`cosh(r) 𝟙`; if each conditional B state had CM `cosh(r′) 𝟙`, the means `m(y)` of B's conditional
states, which are affine in the one real outcome `y`, would need covariance
`(cosh r − cosh r′) 𝟙`, of rank 2, while an affine image of a scalar has covariance of rank at
most 1. So B's correction must include an outcome-independent Gaussian unitary (a squeezer), as
stated here; its symplectic part is fixed and only the displacement uses the communicated
outcome. -/
theorem tmss_degrade_one_local (r r' : ℝ) (hr' : 0 ≤ r') (hlt : r' < r) :
    (∃ (U : AffineMultimodeGaussianUnitary (1 + 1)) (σ : ℝ → DensityKernel (1 + 1))
        (DA DB : ℝ → AffineMultimodeGaussianUnitary 1),
      (∀ y, (DA y).symplecticMatrix = 1) ∧
      (∀ y y', (DB y).symplecticMatrix = (DB y').symplecticMatrix) ∧
      (∀ y, HomodyneLastA (unitaryA U (appendVacuumA (tmssProduct ![r]))) y (σ y)) ∧
      ∀ y, unitaryB (DB y) (unitaryA (DA y) (σ y)) = tmssProduct ![r']) ∧
    OneLocalReach ⟨1, 1, tmssProduct ![r]⟩ ⟨1, 1, tmssProduct ![r']⟩ := by sorry

end GaussianGLOCC
