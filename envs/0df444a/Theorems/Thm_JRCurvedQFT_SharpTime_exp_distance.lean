-- Prove2me | Theorems.Thm_JRCurvedQFT_SharpTime_exp_distance
-- name    : JRCurvedQFT.SharpTime.exp_distance
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T18:40:09.905805+00:00
-- url     : https://prove2.me/theorems/c9be6d52-71c3-46c5-a16e-c08bf7dff960
-- title:
--   Proof of Theorem 4.4, p. 25 — $\|e^{i\Phi(f)}-e^{i\Phi(g)}\|_{\mathcal E}^2=2(1-e^{-\frac12\|f-g\|_{-1}^2})$ (corrected: squared $H_{-1}$ norm in the exponent)
-- statement:
--   Throughout, $M$ is a quantizable static spacetime (Definition 4.1): a complete, connected, smooth Riemannian manifold of dimension $d$ with a global static Killing flow $\phi_s$ (each $\phi_s$ an isometry), a smooth time function $t$ with $t(\phi_s p)=t(p)+s$, the time-zero slice $\Sigma=\{t=0\}$ orthogonal to the Killing field $\xi$, the regions $\Omega_\pm=\{\pm t>0\}$, the reflection $\theta$ and the lapse $F=\langle\xi,\xi\rangle$; $\mathrm{dvol}$ is its Riemannian volume.
--
--   Let $m>0$ and let $\Phi$ be the Euclidean free field of mass $m$ on $(\Omega,P)$. For all $h,k\in H_{-1}(M)$,
--   $$\int\big|e^{i\Phi(h)}-e^{i\Phi(k)}\big|^2\,dP=2\Big(1-e^{-\frac12\|h-k\|_{-1}^2}\Big).$$
--   So the map $h\mapsto e^{i\Phi(h)}$ from $H_{-1}(M)$ to $\mathcal E$ is continuous, which carries $H_{-1}$-limits of test functions to $\mathcal E$-limits of exponential vectors.
--
--   Differences from the source:
--   - correction: 2(1 − e^{−½‖f−g‖₋₁}) → 2(1 − e^{−½‖f−g‖²₋₁}); reason: E|e^{iX} − e^{iY}|² = 2 − 2e^{−½Var(X−Y)} with Var = ‖f−g‖²₋₁; counterexample to the printed form: any f, g with ‖f − g‖₋₁ = 2 (flat ℝ^d, g = 0, f a rescaled bump) gives 2(1 − e^{−2}) ≈ 1.729 ≠ 2(1 − e^{−1}) ≈ 1.264
--   - encoding: H₋₁(M) as the completion of C^∞(M) in ⟨f, Cf⟩, ⟨f, Cg⟩ with C = (−Δ+m²)⁻¹, and dvol → ‖ℓ‖₋₁ = sup of |ℓ(u)| over u ∈ C_c^∞(M) with ∫(|∇u|²+m²u²) dvol ≤ 1, ⟨·, C·⟩ by polarization, dvol characterized by its chart densities √det g; reason: on a complete M, −Δ is essentially self-adjoint on C_c^∞ and this dual norm is ⟨f, Cf⟩^{1/2}; same objects (Reading 4)
--   - generalization: the Gaussian measure µ on H₋∞ with covariance C (Minlos), ℰ = L²(H₋∞, µ) → any isonormal Gaussian field Φ on H₋₁(M) over any probability space (Ω, P), ℰ = L²(Ω, P; ℂ); reason: Minlos’ measure is one such field and every statement depends only on the joint law (Reading 6)
-- source:
--   Jaffe, Ritter, Quantum Field Theory on Curved Backgrounds. I. The Euclidean Functional Integral, arXiv:hep-th/0609003v1, proof of Theorem 4.4, p. 25 (displayed identity)

import Mathlib
import Definitions.Def_JRCurvedQFT_SharpTime_IsRiemannianVolume
import Definitions.Def_JRCurvedQFT_SharpTime_IsGaussianField
import Definitions.Def_JRCurvedQFT_SharpTime_expVec

open scoped Manifold ContDiff ENNReal Topology
open Bundle MeasureTheory

namespace JRCurvedQFT.SharpTime

/-- **Proof of Theorem 4.4, p. 25 (corrected).** The `ℰ`-distance of two exponential vectors:
`∫ |e^{iΦ(f)} − e^{iΦ(g)}|² dµ_C = 2(1 − e^{−½‖f−g‖²₋₁})`.

Jaffe, Ritter, *Quantum Field Theory on Curved Backgrounds. I. The Euclidean Functional Integral*, arXiv:hep-th/0609003v1, proof of Theorem 4.4, p. 25: "The L² norm in ℰ, ∫ |e^{iΦ(f)} − e^{iΦ(g)}|² dµ_C(Φ) =
2(1 − e^{−½‖f−g‖₋₁}), is controlled in terms of the norm ‖ ‖₋₁ on Sobolev space".

Setting (Definition 4.1): `M` is a complete, connected, smooth Riemannian manifold of dimension
`d` (charts in `ℝ^d`, smooth metric, distance = Riemannian distance) with a static structure `S`
(flow `φ_s` of the static Killing field, time function `t`, slice `Σ = {t = 0}`), and `μ` is its
Riemannian volume. `m > 0` and `Φ` is the free field. For `h, k ∈ H₋₁(M)`:
`‖e^{iΦ(h)} − e^{iΦ(k)}‖²_ℰ = 2(1 − e^{−‖h − k‖²₋₁/2})`.

**Formalization Note** Correction: the printed exponent lacks the square of `‖f − g‖₋₁`
(`E|e^{iX} − e^{iY}|² = 2 − 2e^{−½Var(X−Y)}`). -/
theorem exp_distance {d : ℕ} {M : Type} [EMetricSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin d)) M] [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin d)) ∞ M]
    [RiemannianBundle (fun (x : M) ↦ TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin d)) x)]
    [IsContMDiffRiemannianBundle 𝓘(ℝ, EuclideanSpace ℝ (Fin d)) ∞ (EuclideanSpace ℝ (Fin d))
      (fun (x : M) ↦ TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin d)) x)]
    [IsRiemannianManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin d)) M] [CompleteSpace M] [ConnectedSpace M]
    [MeasurableSpace M] [BorelSpace M]
    (μ : Measure M) (hμ : IsRiemannianVolume (d := d) μ)
    (m : ℝ) (hm : 0 < m) {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (Φ : ((M → ℝ) → ℝ) → Ω → ℝ) (hΦ : IsGaussianField (d := d) μ m P Φ)
    (h k : (M → ℝ) → ℝ) (hh : IsHminus1 (d := d) μ m h) (hk : IsHminus1 (d := d) μ m k) :
    ‖expVec P Φ h - expVec P Φ k‖ ^ 2
      = 2 * (1 - Real.exp (-((negSobolevNorm (d := d) μ m (h - k)).toReal ^ 2 / 2))) := by sorry

end JRCurvedQFT.SharpTime
