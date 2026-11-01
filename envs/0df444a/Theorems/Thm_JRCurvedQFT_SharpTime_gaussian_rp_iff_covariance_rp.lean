-- Prove2me | Theorems.Thm_JRCurvedQFT_SharpTime_gaussian_rp_iff_covariance_rp
-- name    : JRCurvedQFT.SharpTime.gaussian_rp_iff_covariance_rp
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T18:38:17.280134+00:00
-- url     : https://prove2.me/theorems/40172759-89ff-4a5e-82dd-9cc7febe3eb2
-- title:
--   §1.6, p. 8 — a Gaussian measure with covariance $T$ is reflection positive iff $T$ is reflection positive (1.11)
-- statement:
--   Throughout, $M$ is a quantizable static spacetime (Definition 4.1): a complete, connected, smooth Riemannian manifold of dimension $d$ with a global static Killing flow $\phi_s$ (each $\phi_s$ an isometry), a smooth time function $t$ with $t(\phi_s p)=t(p)+s$, the time-zero slice $\Sigma=\{t=0\}$ orthogonal to the Killing field $\xi$, the regions $\Omega_\pm=\{\pm t>0\}$, the reflection $\theta$ and the lapse $F=\langle\xi,\xi\rangle$; $\mathrm{dvol}$ is its Riemannian volume.
--
--   Let $T$ be a bounded, positive, self-adjoint operator on real $L^2(M)$ (a covariance), $\Psi$ a Gaussian field with mean zero and covariance $T$ on a probability space $(\Omega,P)$, $\mathcal E=L^2(\Omega,P;\mathbb C)$, $\mathcal E_+$ the closed span of $e^{i\Psi(f)}$ over real $f\in L^2(M)$ vanishing outside $\Omega_+$, and $\Theta$ a unitary of $\mathcal E$ with $\Theta e^{i\Psi(f)}=e^{i\Psi(f\circ\theta)}$ for all $f\in L^2(M)$. Then the following are equivalent:
--
--   1. the Gaussian measure is reflection positive (1.10): $\int\overline{\Theta(F)}\,F\,dP=\langle\Theta F,F\rangle_{\mathcal E}\ge0$ for all $F\in\mathcal E_+$;
--   2. $T$ is reflection positive in the operator sense (1.11): $\langle f,\theta Tf\rangle_{L^2(M)}=\langle f\circ\theta,Tf\rangle_{L^2(M)}\ge0$ for every real $f\in L^2(M)$ vanishing outside $\Omega_+$.
--
--   Here "$\ge0$" for a complex number means real and nonnegative. The free covariance $C=(-\Delta+m^2)^{-1}$ is the case $T=C$.
--
--   Differences from the source:
--   - reading: "A Gaussian measure with mean zero and covariance C" for a time reflection θ (Definitions 1.1, 1.4), with Ω₊ from (1.1) → a manifold with a static structure (Example 1.1), Ω₊ = {t > 0}, θ(p) = φ_{−2t(p)}(p); reason: Ω₊ in (1.10)–(1.11) is defined only through the decomposition (1.1) of Example 1.1 (static manifolds), the case the paper studies
--   - encoding: quantizable static spacetime (Definition 4.1) with Example 1.1 → complete connected Riemannian manifold with a global isometric flow φ_s and a smooth time function with t∘φ_s = t + s and ξ ⟂ ker dt on Σ = {t = 0}; reason: equivalent to Definition 4.1 with the uniqueness of t that Example 1.1 needs (Reading 3)
--   - encoding: covariance C, a bounded operator on L²(M) (1.11), dvol → T : L²(M; ℝ) →L L²(M; ℝ) with T.IsPositive (self-adjoint, ⟨f, Tf⟩ ≥ 0); dvol characterized by its chart densities √det g; reason: a covariance is a positive self-adjoint operator; (1.11) is stated for bounded operators on L²(M); complex f reduce to real ones for a real covariance
--   - generalization: the Gaussian measure µ on H₋∞ with mean zero and covariance C, ℰ = L²(H₋∞, µ) → any family Ψ(f), f ∈ L²(M), on any probability space (Ω, P), a.s. linear with Ψ(f) ~ N(0, ⟨f, Tf⟩), ℰ = L²(Ω, P; ℂ); reason: the measure µ gives such a field (Φ(f) for f ∈ L²(M)), and every statement depends only on the joint law (Reading 6)
--   - reading: E_Ω = span{e^{iΦ(f)} : f ∈ H₋₁(M), supp f ⊂ Ω} (Definition 1.2) for ℰ₊, and supp f ⊆ Ω₊ for f ∈ L²(M) in (1.11) → real f ∈ L²(M) with f = 0 a.e. on {t ≤ 0}, in both; reason: for L² functions the support condition is read as an essential-support condition; for a covariance bounded on L²(M) both sides are L²-continuous in f and functions with closed support in Ω₊ are L²-dense in this class, so the two readings give the same ℰ₊ and the same condition (1.11)
--   - reading: Θ = Γ(θ), the reflection induced on ℰ (Definition 1.4) → every unitary Θ of L²(P) with Θ e^{iΨ(f)} = e^{iΨ(f∘θ)} for all f ∈ L²(M); reason: Γ(θ) is such a unitary whenever θ preserves the covariance (as the free covariance does, θ being an isometry), and every such Θ agrees with Γ(θ) on ℰ; Γ(θ) is a unitary of ℰ only in that case, which is the case where (1.10) is used (Reading 7)
--   - encoding: ⟨f, θTf⟩_{L²(M)} in (1.11) → ⟨g, Tf⟩_{L²(M)} for every g ∈ L²(M) with g = f∘θ a.e.; reason: θ is a measure-preserving involution, so ⟨f, (Tf)∘θ⟩ = ⟨f∘θ, Tf⟩; f∘θ is given as an a.e. class
-- source:
--   Jaffe, Ritter, Quantum Field Theory on Curved Backgrounds. I. The Euclidean Functional Integral, arXiv:hep-th/0609003v1, §1.6, p. 8 (with Definition 1.4, Eqs. (1.10)–(1.11), p. 7)

import Mathlib
import Definitions.Def_JRCurvedQFT_SharpTime_IsRiemannianVolume
import Definitions.Def_JRCurvedQFT_SharpTime_IsCovGaussianField
import Definitions.Def_JRCurvedQFT_SharpTime_positiveTimeSubspaceL2

open scoped Manifold ContDiff ENNReal Topology
open Bundle MeasureTheory

namespace JRCurvedQFT.SharpTime

/-- **§1.6, p. 8.** A Gaussian measure with mean zero and covariance `T` is reflection positive iff
`T` is reflection positive in the operator sense (1.11).

Jaffe, Ritter, *Quantum Field Theory on Curved Backgrounds. I. The Euclidean Functional Integral*, arXiv:hep-th/0609003v1, §1.6, p. 8: "A Gaussian measure with mean zero and covariance C is reflection positive iff C
is reflection positive in the operator sense, eqn. (1.11)." Definition 1.4, p. 7: µ is reflection
positive if `∫ \overline{Θ(F)} F dµ ≥ 0` for all `F ∈ ℰ₊` (1.10); a bounded operator `T` on `L²(M)` is
reflection positive if `supp f ⊆ Ω₊ ⇒ ⟨f, θTf⟩_{L²(M)} ≥ 0` (1.11).

Setting (Definition 4.1 and Example 1.1): `M` is a complete, connected, smooth Riemannian manifold
of dimension `d` (charts in `ℝ^d`, smooth metric, distance = Riemannian distance) with a static
structure `S` (flow `φ_s` of the static Killing field, time function `t`, slice `Σ = {t = 0}`,
reflection `θ`, `Ω₊ = {t > 0}`), and `μ` is its Riemannian volume. `T` is a bounded, positive,
self-adjoint operator on real `L²(M)` (a covariance), `Ψ` is a Gaussian field with mean zero and
covariance `T` over a probability space `(Ω, P)`, and `Θ = Γ(θ)` is a unitary of `ℰ = L²(Ω, P; ℂ)`
with `Θ e^{iΨ(f)} = e^{iΨ(f ∘ θ)}` for every `f ∈ L²(M)`.
Statement: `(∀ F ∈ ℰ₊, ⟨ΘF, F⟩_ℰ ≥ 0)` iff `(∀ real f ∈ L²(M) vanishing a.e. outside Ω₊,
⟨f, θTf⟩_{L²(M)} ≥ 0)`, where `⟨f, θTf⟩ = ⟨f ∘ θ, Tf⟩` because `θ` is a measure-preserving involution.

**Formalization Note** `∫ \overline{ΘF} F dµ` is Mathlib's `⟪ΘF, F⟫` (conjugate-linear in the first
slot); "≥ 0" for a complex number means real part `≥ 0` and imaginary part `0`. `f ∘ θ` is any
`L²` element `g` with `g = f ∘ θ` a.e. Reading 7: `Θ` is characterized on all exponential vectors and
is otherwise arbitrary. The covariance is arbitrary (not only `(−Δ + m²)⁻¹`), as in the sentence on
p. 8; the free covariance is the case `T = C`. -/
theorem gaussian_rp_iff_covariance_rp {d : ℕ} {M : Type} [EMetricSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin d)) M] [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin d)) ∞ M]
    [RiemannianBundle (fun (x : M) ↦ TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin d)) x)]
    [IsContMDiffRiemannianBundle 𝓘(ℝ, EuclideanSpace ℝ (Fin d)) ∞ (EuclideanSpace ℝ (Fin d))
      (fun (x : M) ↦ TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin d)) x)]
    [IsRiemannianManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin d)) M] [CompleteSpace M] [ConnectedSpace M]
    [MeasurableSpace M] [BorelSpace M]
    (S : StaticStructure (d := d) M) (μ : Measure M) (hμ : IsRiemannianVolume (d := d) μ)
    (T : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ) (hT : T.IsPositive)
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (Ψ : Lp ℝ 2 μ → Ω → ℝ) (hΨ : IsCovGaussianField μ T P Ψ)
    (Θ : Lp ℂ 2 P ≃ₗᵢ[ℂ] Lp ℂ 2 P)
    (hΘ : ∀ f g : Lp ℝ 2 μ, (g =ᵐ[μ] fun p => f (S.reflection p)) →
      Θ (expVec P Ψ f) = expVec P Ψ g) :
    (∀ A ∈ positiveTimeSubspaceL2 S μ P Ψ,
      0 ≤ (inner ℂ (Θ A) A).re ∧ (inner ℂ (Θ A) A).im = 0) ↔
    (∀ f g : Lp ℝ 2 μ, (∀ᵐ p ∂μ, S.time p ≤ 0 → f p = 0) →
      (g =ᵐ[μ] fun p => f (S.reflection p)) → 0 ≤ inner ℝ g (T f)) := by sorry

end JRCurvedQFT.SharpTime
