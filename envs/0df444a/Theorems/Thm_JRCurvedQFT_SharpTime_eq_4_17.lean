-- Prove2me | Theorems.Thm_JRCurvedQFT_SharpTime_eq_4_17
-- name    : JRCurvedQFT.SharpTime.eq_4_17
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T18:41:13.099314+00:00
-- url     : https://prove2.me/theorems/a0027eb7-3cb9-425e-8b75-719d78feecc4
-- title:
--   Eqs. (4.17)–(4.19) — moving sharp-time vectors to time zero: $\Pi(:e^{i\Phi(\sum_k (f_k)_{\tau_k})}:)=\Pi(:e^{i\Phi(\sum_k (f_k^{\tau_k})_0)}:)$, $f^\tau=F^{-1/2}e^{-\tau\omega}F^{1/2}f$
-- statement:
--   Throughout, $M$ is a quantizable static spacetime (Definition 4.1): a complete, connected, smooth Riemannian manifold of dimension $d$ with a global static Killing flow $\phi_s$ (each $\phi_s$ an isometry), a smooth time function $t$ with $t(\phi_s p)=t(p)+s$, the time-zero slice $\Sigma=\{t=0\}$ orthogonal to the Killing field $\xi$, the regions $\Omega_\pm=\{\pm t>0\}$, the reflection $\theta$ and the lapse $F=\langle\xi,\xi\rangle$; $\mathrm{dvol}$ is its Riemannian volume.
--
--   Let $m>0$, $\Phi$ the Euclidean free field, $\Theta$ a unitary of $\mathcal E$ with $\Theta e^{i\Phi(h)}=e^{i\Phi(\theta^*h)}$ for all $h\in H_{-1}(M)$, $\mathcal H$ an Osterwalder–Schrader completion of $(\mathcal E_+,\Theta)$ with quantization map $\Pi$, and $\omega^2$ the Friedrichs extension of $F^{1/2}(-Q+m^2)F^{1/2}$ with projection-valued measure $P_\omega$. For real $f_1,\dots,f_n\in C_c^\infty(\Sigma)$ and times $\tau_1,\dots,\tau_n>0$, put $f_k^{\tau_k}=F^{-1/2}e^{-\tau_k\omega}F^{1/2}f_k$ (4.18). Then:
--
--   1. each time-zero distribution $(f_k^{\tau_k})_0$ lies in $H_{-1}(M)$;
--   2. both Wick exponentials below lie in $\mathcal E_+$, and
--   $$\Pi\Big(:\!e^{i\Phi(\sum_k (f_k)_{\tau_k})}\!:\Big)=\Pi\Big(:\!e^{i\Phi(\sum_k (f_k^{\tau_k})_0)}\!:\Big),$$
--   i.e. $\langle\hat A,:\exp(i\Phi(\sum_k(f_k)_{\tau_k})):\hat{}\rangle_{\mathcal H}=\langle\hat A,:\exp(i\Phi(\sum_k(f_k^{\tau_k})_0)):\hat{}\rangle_{\mathcal H}$ for every $A\in\mathcal E_+$ ((4.17) for $n=1$).
--
--   Every positive-time Wick exponential of sharp-time fields is thus represented in $\mathcal H$ by a time-zero vector.
--
--   Differences from the source:
--   - generalization: (4.17) for a single sharp-time vector :exp(iΦ(f_t)): → finite sums Σ_k (f_k)_{τ_k} with τ_k > 0 (n = 1 is the printed case); reason: the corrected density step (multi-time exponentials) needs it; it follows from (4.9) by linearity in the test function exactly as (4.19)
--   - encoding: ⟨Â, X̂⟩_ℋ = ⟨Â, Ŷ⟩_ℋ for all A → Π X = Π Y, with X, Y ∈ ℰ₊ asserted; reason: equality of all inner products with a dense set is equality in ℋ
--   - encoding: f^t₀(p, t′) = δ(t′)(F^{−1/2}e^{−tω}F^{1/2}f)(p) → the functional u ↦ ⟨F^{−1/2}u, e^{−τω}F^{1/2}f⟩_{𝒦_Σ} with e^{−τω} computed in the spectral calculus of ω², and its membership in H₋₁(M) concluded; reason: f^τ is generally not C_c^∞, so its time-zero distribution is defined by its pairing with test functions
--   - reading: the class of f is not specified (the proof writes g ∈ 𝒯_Σ, never defined) → real f ∈ C_c^∞(Σ), encoded by smooth ξ-invariant lifts f : M → ℝ with Σ ∩ tsupport f compact; reason: smallest natural class; it makes density hardest and isometry/membership extend to closures (Reading 2)
--   - encoding: quantizable static spacetime (Definition 4.1) with Example 1.1 → complete connected Riemannian manifold with a global isometric flow φ_s and a smooth time function with t∘φ_s = t + s and ξ ⟂ ker dt on Σ = {t = 0}; reason: equivalent to Definition 4.1 with the uniqueness of t that Example 1.1 needs (Reading 3)
--   - encoding: H₋₁(M) as the completion of C^∞(M) in ⟨f, Cf⟩, ⟨f, Cg⟩ with C = (−Δ+m²)⁻¹, and dvol → ‖ℓ‖₋₁ = sup of |ℓ(u)| over u ∈ C_c^∞(M) with ∫(|∇u|²+m²u²) dvol ≤ 1, ⟨·, C·⟩ by polarization, dvol characterized by its chart densities √det g; reason: on a complete M, −Δ is essentially self-adjoint on C_c^∞ and this dual norm is ⟨f, Cf⟩^{1/2}; same objects (Reading 4)
--   - generalization: the Gaussian measure µ on H₋∞ with covariance C (Minlos), ℰ = L²(H₋∞, µ) → any isonormal Gaussian field Φ on H₋₁(M) over any probability space (Ω, P), ℰ = L²(Ω, P; ℂ); reason: Minlos’ measure is one such field and every statement depends only on the joint law (Reading 6)
--   - generalization: Θ = Γ(θ) and ℋ the completion of ℰ₊/𝒩 with (A, B) = ⟨ΘA, B⟩ → every unitary Θ of L²(P) with Θe^{iΦ(h)} = e^{iΦ(θ*h)} for all h ∈ H₋₁(M), and every OS completion (dense-range linear Π with ⟨ΠA, ΠB⟩ = ⟨A, ΘB⟩); reason: Γ(θ) and the quotient completion are instances, and every such Θ agrees with Γ(θ) on ℰ (Reading 7)
--   - reading: "we choose a self-adjoint extension ... we may choose the Friedrichs extension" → ω² is the Friedrichs extension of F^{1/2}(−Q+m²)F^{1/2} on C_c^∞(Σ) (characterized: self-adjoint, extends it, domain inside the form closure); ω enters through the spectral calculus of ω², with the projection-valued measure Pω; reason: the paper picks the Friedrichs extension for definiteness; other extensions can give a different ω (Reading 8)
-- source:
--   Jaffe, Ritter, Quantum Field Theory on Curved Backgrounds. I. The Euclidean Functional Integral, arXiv:hep-th/0609003v1, Eqs. (4.17)–(4.19), pp. 25–26

import Mathlib
import Definitions.Def_JRCurvedQFT_SharpTime_IsRiemannianVolume
import Definitions.Def_JRCurvedQFT_SharpTime_IsGaussianField
import Definitions.Def_JRCurvedQFT_SharpTime_thetaStar
import Definitions.Def_JRCurvedQFT_SharpTime_positiveTimeSubspace
import Definitions.Def_JRCurvedQFT_SharpTime_wickExp
import Definitions.Def_JRCurvedQFT_SharpTime_sharpTime
import Definitions.Def_JRCurvedQFT_SharpTime_IsOmegaSq
import Definitions.Def_JRCurvedQFT_SharpTime_shiftedTimeZero
import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P17
import Definitions.Def_TeschlQM_Shared_IsProjValuedMeasure
import Definitions.Def_TeschlQM_Spectral_spectralIntegral

open scoped Manifold ContDiff ENNReal Topology
open Bundle MeasureTheory

namespace JRCurvedQFT.SharpTime

/-- **Eqs. (4.17)–(4.19) (generalized to multi-time sums).** Moving sharp-time vectors to time zero:
`Π(:exp(iΦ(Σ_k (f_k)_{τ_k})):) = Π(:exp(iΦ(Σ_k (f_k^{τ_k})₀)):)` with `f^τ = F^{−1/2} e^{−τω} F^{1/2} f`.

Jaffe, Ritter, *Quantum Field Theory on Curved Backgrounds. I. The Euclidean Functional Integral*, arXiv:hep-th/0609003v1, pp. 25–26: "Equation (4.14) is proved by means of the following identity:
⟨Â, :exp(iΦ(f_t)):^⟩_ℋ = ⟨Â, :exp(iΦ(f^t₀)):^⟩_ℋ (4.17) where f^t := (F^{−1/2}e^{−tω}F^{1/2})f,
(4.18) where f is a function on Σ, and hence so is f^t", proved through (4.19) and Theorem 4.3.

Setting (Definition 4.1): `M` is a complete, connected, smooth Riemannian manifold of dimension
`d` (charts in `ℝ^d`, smooth metric, distance = Riemannian distance) with a static structure `S`
(flow `φ_s` of the static Killing field, time function `t`, slice `Σ = {t = 0}`), and `μ` is its
Riemannian volume. `m > 0`, `Φ` is the free field, `Θ` is a unitary of `ℰ` with `Θe^{iΦ(h)} = e^{iΦ(θ^*h)}`,
`H` is an OS completion of `(ℰ₊, Θ)` with quotient map `Π`, `A = ω²` (Friedrichs extension) with
projection-valued measure `Pω`. For real test functions `f_k` on `Σ` and times `τ_k > 0`:
1. each `(f_k^{τ_k})₀` lies in `H₋₁(M)`;
2. both Wick exponentials lie in `ℰ₊` and have the same image under `Π`.

**Formalization Note** Equality in `ℋ` is (4.17) for all `Â`. The printed case is `n = 1`; the
multi-time form is what the corrected density step (milestone `multiTime_dense`) needs, and it
follows from (4.9) by linearity in the test function exactly as (4.19). -/
theorem eq_4_17 {d : ℕ} {M : Type} [EMetricSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin d)) M] [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin d)) ∞ M]
    [RiemannianBundle (fun (x : M) ↦ TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin d)) x)]
    [IsContMDiffRiemannianBundle 𝓘(ℝ, EuclideanSpace ℝ (Fin d)) ∞ (EuclideanSpace ℝ (Fin d))
      (fun (x : M) ↦ TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin d)) x)]
    [IsRiemannianManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin d)) M] [CompleteSpace M] [ConnectedSpace M]
    [MeasurableSpace M] [BorelSpace M]
    (S : StaticStructure (d := d) M) (μ : Measure M) (hμ : IsRiemannianVolume (d := d) μ)
    (m : ℝ) (hm : 0 < m) {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (Φ : ((M → ℝ) → ℝ) → Ω → ℝ) (hΦ : IsGaussianField (d := d) μ m P Φ)
    (Θ : Lp ℂ 2 P ≃ₗᵢ[ℂ] Lp ℂ 2 P)
    (hΘ : ∀ h, IsHminus1 (d := d) μ m h → Θ (expVec P Φ h) = expVec P Φ (thetaStar S h))
    (H : QAlgorithms.Papers.Independent.Intake100.P17.OSCompletion
      (positiveTimeSubspace S μ P Φ) Θ)
    (A : Lp ℂ 2 (sliceMeasure S μ) →ₗ.[ℂ] Lp ℂ 2 (sliceMeasure S μ)) (hA : IsOmegaSq S μ m A)
    (Pω : Set ℝ → (Lp ℂ 2 (sliceMeasure S μ) →L[ℂ] Lp ℂ 2 (sliceMeasure S μ)))
    (hP : TeschlQM.Shared.IsProjValuedMeasure Pω)
    (hAP : A = TeschlQM.Spectral.spectralIntegral Pω (fun x => (x : ℂ)))
    (n : ℕ) (f : Fin n → M → ℝ) (τ : Fin n → ℝ) (hf : ∀ k, IsSliceTestFunction S (f k) ∧ 0 < τ k) :
    (∀ k, IsHminus1 (d := d) μ m (shiftedTimeZero S μ Pω (τ k) (f k))) ∧
    ∃ (h₁ : wickExp (d := d) μ m P Φ (∑ k, sharpTime S μ (f k) (τ k))
          ∈ positiveTimeSubspace S μ P Φ)
      (h₂ : wickExp (d := d) μ m P Φ (∑ k, shiftedTimeZero S μ Pω (τ k) (f k))
          ∈ positiveTimeSubspace S μ P Φ),
      H.quotientMap ⟨_, h₁⟩ = H.quotientMap ⟨_, h₂⟩ := by sorry

end JRCurvedQFT.SharpTime
