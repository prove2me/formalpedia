-- Prove2me | Theorems.Thm_HamLocality237_Testing_propagator
-- name    : HamLocality237.Testing.propagator
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-11T04:37:25.3392+00:00
-- url     : https://prove2.me/theorems/cd841247-c298-4812-9005-cd2a0cf83ff8
-- title:
--   §2.2 — Dyson propagator and observable identity
-- statement:
--   Let $E$ be a complex Hilbert space, including the infinite-dimensional case, and let $t_f\ge0$. Suppose $F$ is strongly measurable, integrable in operator norm on $[0,t_f]$, and self-adjoint almost everywhere. For the ordered Dyson terms and their series $U_F$,
--
--   $$\|D_m(t)\|\le\frac{\ell^m}{m!},\qquad \ell=\int_0^{t_f}\|F(s)\|\,ds.$$
--
--   The series converges absolutely at each time and uniformly on the whole interval. It is the unique absolutely continuous solution of $U_F(t)=I-i\int_0^tF(s)U_F(s)\,ds$, with integrable integrand. Almost everywhere it satisfies $\dot U_F=-iFU_F$, and it is unitary at every time. For every bounded operator $B$ and initial vector $v$, writing $\psi(t)=U_F(t)v$,
--
--   $$\frac d{dt}\langle\psi(t),B\psi(t)\rangle=\langle\psi(t),i[F(t),B]\psi(t)\rangle$$
--
--   almost everywhere. This supplies both the finite algorithm evolutions and the infinite-dimensional purified evolutions.
--
--   Differences from the source:
--   - encoding: multiple integrals over ordered time simplices and a propagator starting at time zero → recursive ordered integrals including the identity as term zero; HasSum, uniform convergence, and uniqueness restricted to the stated interval; reason: nesting the latest time outside gives exactly the ordered simplex formula; off-interval extensions do not affect the claim
--   - generalization: the observable identity for a bounded observable → the identity for every bounded complex-linear operator and every initial vector; reason: the identity is valid without self-adjointness of the observable or normalization of the initial vector and specializes to every source observable and state
-- source:
--   Francisco Escudero Gutiérrez, Junseo Lee, Sebastian Zur, STOC 2027 submission #237 (October 2026), §2.2 Eqs. (2)–(3), p.9. https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/237.pdf

import Definitions.Def_HamLocality237_Testing_Dynamics

open MeasureTheory Filter
open scoped BigOperators Topology

namespace HamLocality237.Testing

/-- §2.2 Eqs. (2)--(3), including infinite-dimensional Hilbert spaces. -/
theorem propagator {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [CompleteSpace E] (tf : ℝ) (htf : 0 ≤ tf) (F : ℝ → E →L[ℂ] E)
    (hF : IntegrableOn F (Set.Icc 0 tf))
    (hsa : ∀ᵐ t ∂volume.restrict (Set.Icc 0 tf), IsSelfAdjoint (F t)) :
    (∀ m t, t ∈ Set.Icc 0 tf →
      ‖dysonTerm F m t‖ ≤ (∫ s in (0 : ℝ)..tf, ‖F s‖) ^ m / (Nat.factorial m : ℝ)) ∧
    (∀ t ∈ Set.Icc 0 tf, Summable (fun m => ‖dysonTerm F m t‖) ∧
      HasSum (fun m => dysonTerm F m t) (dysonEvolution F t)) ∧
    TendstoUniformlyOn (fun N t => ∑ m ∈ Finset.range N, dysonTerm F m t)
      (dysonEvolution F) atTop (Set.Icc 0 tf) ∧
    IsPropagator F (dysonEvolution F) tf ∧
    (∀ V : ℝ → E →L[ℂ] E, IsPropagator F V tf →
      Set.EqOn V (dysonEvolution F) (Set.Icc 0 tf)) ∧
    (∀ᵐ t ∂volume.restrict (Set.Icc 0 tf),
      HasDerivAt (dysonEvolution F) ((-Complex.I) • (F t * dysonEvolution F t)) t) ∧
    (∀ t ∈ Set.Icc 0 tf,
      (dysonEvolution F t).adjoint * dysonEvolution F t = 1 ∧
      dysonEvolution F t * (dysonEvolution F t).adjoint = 1) ∧
    (∀ (B : E →L[ℂ] E) (v : E), ∀ᵐ t ∂volume.restrict (Set.Icc 0 tf),
      HasDerivAt (fun s => inner ℂ (dysonEvolution F s v) (B (dysonEvolution F s v)))
        (inner ℂ (dysonEvolution F t v)
          ((Complex.I • (F t * B - B * F t)) (dysonEvolution F t v))) t) := by sorry

end HamLocality237.Testing
