-- Prove2me | Theorems.Thm_JRCurvedQFT_SharpTime_theorem_4_3
-- name    : JRCurvedQFT.SharpTime.theorem_4_3
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T18:40:57.101039+00:00
-- url     : https://prove2.me/theorems/09935060-40ec-44bc-b127-804bb5610309
-- title:
--   Theorem 4.3 (Localization of sharp-time integrals) — $\langle f_t,Cg_s\rangle_M=\langle f,F^{1/2}\frac{e^{-|t-s|\omega}}{2\omega}F^{1/2}g\rangle_{\mathcal K_\Sigma}$, and $C$ is reflection positive
-- statement:
--   Throughout, $M$ is a quantizable static spacetime (Definition 4.1): a complete, connected, smooth Riemannian manifold of dimension $d$ with a global static Killing flow $\phi_s$ (each $\phi_s$ an isometry), a smooth time function $t$ with $t(\phi_s p)=t(p)+s$, the time-zero slice $\Sigma=\{t=0\}$ orthogonal to the Killing field $\xi$, the regions $\Omega_\pm=\{\pm t>0\}$, the reflection $\theta$ and the lapse $F=\langle\xi,\xi\rangle$; $\mathrm{dvol}$ is its Riemannian volume.
--
--   Let $m>0$, $C=(-\Delta+m^2)^{-1}$, $\mu^2=-Q+m^2$, and let $\omega^2=\sqrt F\mu^2\sqrt F$ be the Friedrichs extension in $\mathcal K_\Sigma$ of $F^{1/2}(-Q+m^2)F^{1/2}$ on $C_c^\infty(\Sigma)$, with projection-valued measure $P_\omega$; $\omega=(\omega^2)^{1/2}$. For real $f,g\in C_c^\infty(\Sigma)$ and $t,s\in\mathbb R$:
--
--   1. the sharp-time distribution $f_t$ lies in $H_{-1}(M)$;
--   2. for every $\tau$, $\lambda\mapsto e^{-|\tau|\sqrt\lambda}/(2\sqrt\lambda)$ is integrable for the spectral measure of $F^{1/2}f$;
--   3. (4.9):
--   $$\langle f_t,Cg_s\rangle_M=\Big\langle f,\ F^{1/2}\frac{e^{-|t-s|\omega}}{2\omega}F^{1/2}g\Big\rangle_{\mathcal K_\Sigma},$$
--   the right side being the spectral integral of $e^{-|t-s|\sqrt\lambda}/(2\sqrt\lambda)$ against the spectral measure of the pair $(F^{1/2}f,F^{1/2}g)$;
--   4. $C$ is reflection positive on $L^2(M)$ (1.11): $\langle f,\theta Cf\rangle_{L^2(M)}\ge0$ for every real $f\in L^2(M)$ vanishing outside $\Omega_+$.
--
--   Differences from the source:
--   - reading: the class of f is not specified (the proof writes g ∈ 𝒯_Σ, never defined) → real f ∈ C_c^∞(Σ), encoded by smooth ξ-invariant lifts f : M → ℝ with Σ ∩ tsupport f compact; reason: smallest natural class; it makes density hardest and isometry/membership extend to closures (Reading 2)
--   - encoding: quantizable static spacetime (Definition 4.1) with Example 1.1 → complete connected Riemannian manifold with a global isometric flow φ_s and a smooth time function with t∘φ_s = t + s and ξ ⟂ ker dt on Σ = {t = 0}; reason: equivalent to Definition 4.1 with the uniqueness of t that Example 1.1 needs (Reading 3)
--   - encoding: H₋₁(M) as the completion of C^∞(M) in ⟨f, Cf⟩, ⟨f, Cg⟩ with C = (−Δ+m²)⁻¹, and dvol → ‖ℓ‖₋₁ = sup of |ℓ(u)| over u ∈ C_c^∞(M) with ∫(|∇u|²+m²u²) dvol ≤ 1, ⟨·, C·⟩ by polarization, dvol characterized by its chart densities √det g; reason: on a complete M, −Δ is essentially self-adjoint on C_c^∞ and this dual norm is ⟨f, Cf⟩^{1/2}; same objects (Reading 4)
--   - reading: "we choose a self-adjoint extension ... we may choose the Friedrichs extension" → ω² is the Friedrichs extension of F^{1/2}(−Q+m²)F^{1/2} on C_c^∞(Σ) (characterized: self-adjoint, extends it, domain inside the form closure); ω enters through the spectral calculus of ω², with the projection-valued measure Pω; reason: the paper picks the Friedrichs extension for definiteness; other extensions can give a different ω (Reading 8)
--   - encoding: f, g in (4.9) ("for simplicity of notation, assume f is real-valued") → real f, g; reason: both sides of (4.9) are sesquilinear, so the complex case follows
--   - encoding: (4.9) with the operator e^{−|t−s|ω}(2ω)⁻¹ applied to F^{1/2}g → the spectral form ∫ e^{−|t−s|√λ}/(2√λ) dμ_{F^{1/2}f, F^{1/2}g}(λ) of the projection-valued measure of ω², together with conclusions 1–2 (f_t ∈ H₋₁(M) and integrability); reason: φ(ω) = φ(√(ω²)); the form version is meaningful even when F^{1/2}g is not in the operator domain, and the finiteness the paper uses implicitly is stated
--   - reading: supp f ⊆ Ω₊ for f ∈ L²(M) in (1.11) → real f ∈ L²(M) with f = 0 a.e. on {t ≤ 0}; reason: for an L² function the support condition is read as an essential-support condition; both versions are equivalent because f ↦ ⟨f, θCf⟩ is L²-continuous and f·1_{t>ε} → f
-- source:
--   Jaffe, Ritter, Quantum Field Theory on Curved Backgrounds. I. The Euclidean Functional Integral, arXiv:hep-th/0609003v1, Theorem 4.3, p. 23 (with (1.11), p. 7)

import Mathlib
import Definitions.Def_JRCurvedQFT_SharpTime_IsRiemannianVolume
import Definitions.Def_JRCurvedQFT_SharpTime_IsOmegaSq
import Definitions.Def_JRCurvedQFT_SharpTime_sharpTime
import Definitions.Def_JRCurvedQFT_SharpTime_IsHminus1
import Definitions.Def_JRCurvedQFT_SharpTime_negSobolevInner
import Definitions.Def_JRCurvedQFT_SharpTime_ofFunction
import Definitions.Def_TeschlQM_Shared_IsProjValuedMeasure
import Definitions.Def_TeschlQM_Spectral_spectralIntegral

open scoped Manifold ContDiff ENNReal Topology
open Bundle MeasureTheory

namespace JRCurvedQFT.SharpTime

/-- **Theorem 4.3 (Localization of sharp-time integrals).**
`⟨f_t, C g_s⟩_M = ⟨f, (F^{1/2} e^{−|t−s|ω}/(2ω) F^{1/2}) g⟩_{𝒦_Σ}`, and `C` is reflection positive.

Jaffe, Ritter, *Quantum Field Theory on Curved Backgrounds. I. The Euclidean Functional Integral*, arXiv:hep-th/0609003v1, §4.4, Theorem 4.3, p. 23: "Let M be a quantizable static spacetime (definition 4.1). Then:
⟨f_t, C g_s⟩_M = ⟨f, (F^{1/2} e^{−|t−s|ω}/(2ω) F^{1/2}) g⟩_{𝒦_Σ}, (4.9) where µ = (−Q + m²)^{1/2} and
ω = (√F µ² √F)^{1/2}. Hence C is reflection positive on L²(M)."

Setting (Definition 4.1): `M` is a complete, connected, smooth Riemannian manifold of dimension
`d` (charts in `ℝ^d`, smooth metric, distance = Riemannian distance) with a static structure `S`
(flow `φ_s` of the static Killing field, time function `t`, slice `Σ = {t = 0}`), and `μ` is its
Riemannian volume. `m > 0`; `A = ω²` is the Friedrichs extension of `F^{1/2}(−Q+m²)F^{1/2}` on `C_c^∞(Σ)`, and
`Pω` is its projection-valued measure (`A = ∫ λ dPω(λ)`).
Conclusions, for real test functions `f, g` on `Σ`:
1. every sharp-time distribution `f_t` lies in `H₋₁(M)`;
2. `λ ↦ e^{−|τ|√λ}/(2√λ)` is integrable for the spectral measure of `F^{1/2} f` (so the right side
   of (4.9) is finite);
3. (4.9): `⟨f_t, C g_s⟩_M` equals the spectral form `∫ e^{−|t−s|√λ}/(2√λ) dμ_{F^{1/2}f, F^{1/2}g}(λ)`,
   which is `⟨F^{1/2} f, e^{−|t−s|ω}(2ω)⁻¹ F^{1/2} g⟩_{𝒦_Σ}`;
4. (1.11), p. 7: for every real `f ∈ L²(M)` vanishing a.e. outside `Ω₊`, `⟨f, θCf⟩_{L²(M)} ≥ 0`.

**Formalization Note** `⟨f, Cg⟩_{L²(M)}` is the `H₋₁` inner product (Reading 4). `ω` enters through
the spectral calculus of `ω²`: `φ(ω) = φ(√(ω²))`; `ω²` has no kernel (`ω² ≥ m²F > 0`), so the value
of `1/(2√λ)` at `λ = 0` (a null set) does not matter. `⟨f, θCf⟩ = ⟨f ∘ θ, Cf⟩` since `θ` preserves
`dvol`. -/
theorem theorem_4_3 {d : ℕ} {M : Type} [EMetricSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin d)) M] [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin d)) ∞ M]
    [RiemannianBundle (fun (x : M) ↦ TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin d)) x)]
    [IsContMDiffRiemannianBundle 𝓘(ℝ, EuclideanSpace ℝ (Fin d)) ∞ (EuclideanSpace ℝ (Fin d))
      (fun (x : M) ↦ TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin d)) x)]
    [IsRiemannianManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin d)) M] [CompleteSpace M] [ConnectedSpace M]
    [MeasurableSpace M] [BorelSpace M]
    (S : StaticStructure (d := d) M) (μ : Measure M) (hμ : IsRiemannianVolume (d := d) μ)
    (m : ℝ) (hm : 0 < m)
    (A : Lp ℂ 2 (sliceMeasure S μ) →ₗ.[ℂ] Lp ℂ 2 (sliceMeasure S μ)) (hA : IsOmegaSq S μ m A)
    (Pω : Set ℝ → (Lp ℂ 2 (sliceMeasure S μ) →L[ℂ] Lp ℂ 2 (sliceMeasure S μ)))
    (hP : TeschlQM.Shared.IsProjValuedMeasure Pω)
    (hAP : A = TeschlQM.Spectral.spectralIntegral Pω (fun x => (x : ℂ))) :
    (∀ f, IsSliceTestFunction S f → ∀ t : ℝ, IsHminus1 (d := d) μ m (sharpTime S μ f t)) ∧
    (∀ f, IsSliceTestFunction S f → ∀ τ : ℝ,
      Integrable (fun l : ℝ => Real.exp (-(|τ| * Real.sqrt l)) / (2 * Real.sqrt l))
        (TeschlQM.Spectral.spectralMeasure Pω
          (toKSigma (sliceMeasure S μ) (fun x => (Real.sqrt (S.lapse x) * f x : ℝ))))) ∧
    (∀ f g, IsSliceTestFunction S f → IsSliceTestFunction S g → ∀ t s : ℝ,
      (negSobolevInner (d := d) μ m (sharpTime S μ f t) (sharpTime S μ g s) : ℂ)
        = TeschlQM.Spectral.spectralForm Pω
          (toKSigma (sliceMeasure S μ) (fun x => (Real.sqrt (S.lapse x) * f x : ℝ)))
          (toKSigma (sliceMeasure S μ) (fun x => (Real.sqrt (S.lapse x) * g x : ℝ)))
          (fun l => (Real.exp (-(|t - s| * Real.sqrt l)) / (2 * Real.sqrt l) : ℝ))) ∧
    (∀ f : M → ℝ, MemLp f 2 μ → (∀ᵐ p ∂μ, S.time p ≤ 0 → f p = 0) →
      0 ≤ negSobolevInner (d := d) μ m (ofFunction μ (f ∘ S.reflection)) (ofFunction μ f)) := by sorry

end JRCurvedQFT.SharpTime
