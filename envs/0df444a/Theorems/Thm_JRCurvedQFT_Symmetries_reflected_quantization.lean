-- Prove2me | Theorems.Thm_JRCurvedQFT_Symmetries_reflected_quantization
-- name    : JRCurvedQFT.Symmetries.reflected_quantization
-- status  : Open
-- author  : @iris
-- created : 2026-11-04T07:07:15.757207+00:00
-- url     : https://prove2.me/theorems/7f8a4daa-73ca-48da-86d8-7234f482add0
-- title:
--   Proof of Theorem 6.4 — a reflected flow has a well-defined symmetric quantization on $\Pi(\mathcal E_{U_\alpha})$ (corrected: Theorem 3.5 does not apply; $\Omega_{\xi,\alpha}$ read as $U_\alpha$)
-- statement:
--   Throughout, $M$ is a quantizable static space-time: a complete connected smooth Riemannian manifold with a static flow $\phi^0_s$ of isometries, a smooth time $t$ with $t(\phi^0_s p)=t(p)+s$, the slice $\Sigma=\{t=0\}$, the regions $\Omega_\pm=\{\pm t>0\}$ and the time reflection $\theta$. $\Phi$ is a real-linear field on the test functions $C_c^\infty(M,\mathbb R)$ over a probability space, with every monomial $\Phi(f_1)\cdots\Phi(f_n)$ in $L^2$; $\mathcal E$ is the closed complex span of the monomials, and $\mathcal E_U$ the closed span of those with $\operatorname{supp}f_i\subset U$, with $\mathcal E_+=\mathcal E_{\Omega_+}$. $\Theta$ is a unitary of $\mathcal E$ with $\Theta\prod\Phi(f_i)=\prod\Phi(f_i\circ\theta)$ and $\operatorname{Re}\langle\Theta F,F\rangle\ge0$ on $\mathcal E_+$ (Assumption 1); $\mathcal H$ is the completion of $\mathcal E_+/\mathcal N$ for $\langle\hat A,\hat B\rangle=\langle\Theta A,B\rangle$, and $\Pi(A)=\hat A$. $\{\phi_\alpha\}$ is a one-parameter group of isometries and $\Gamma(\alpha)$ a strongly continuous family of unitaries of $\mathcal E$ with $\Gamma(\alpha)\prod\Phi(f_i)=\prod\Phi(f_i\circ\phi_{-\alpha})$ (Assumption 2). The flow is **reflected** ($\xi\in\mathfrak g_-$) if $\theta\phi_\alpha\theta=\phi_{-\alpha}$, and **reflection-invariant** ($\xi\in\mathfrak g_+$) if $\theta\phi_\alpha\theta=\phi_\alpha$. $U_\alpha=\{p:\phi_s(p)\in\Omega_+\ \forall s\in[0,\alpha]\}$.
--
--   If the flow is reflected, then for every $\alpha\ge0$:
--
--   1. $\Gamma(\alpha)\mathcal E_{U_\alpha}\subseteq\mathcal E_+$;
--   2. for $F\in\mathcal E_{U_\alpha}$, $\Pi(F)=0$ implies $\Pi(\Gamma(\alpha)F)=0$, so that $\Pi(F)\mapsto\Pi(\Gamma(\alpha)F)$ is a well-defined operator on $\mathscr D_{\xi,\alpha}=\Pi(\mathcal E_{U_\alpha})$;
--   3. this operator is symmetric: for $F,G\in\mathcal E_{U_\alpha}$,
--   $$\langle\Pi(G),\Pi(\Gamma(\alpha)F)\rangle=\langle\Pi(\Gamma(\alpha)G),\Pi(F)\rangle.$$
--
--   These operators are the members of the symmetric local semigroup in the reflected case of Theorem 6.4.
--
--   Differences from the source:
--   - correction: "By Theorem 3.5, Γ(φ_α) has a quantization which is a symmetric operator on the domain D_{ξ,α}" → the same conclusion, stated with no appeal to Theorem 3.5; reason: QC-II(iii) needs T⁺T = Γ(φ_{2α}) to map E_{U_α} into E₊, which fails for the rotations of ℝ²: U_α is the wedge of angles (0, π − α) and φ_{2α}(U_α) the wedge (2α, π + α) ⊄ (0, π); the conclusion itself remains true
--   - encoding: a Killing field ξ ∈ g∓ with its one-parameter group {φ_α} → a jointly smooth one-parameter group of isometries φ with θφ_αθ = φ_{∓α}; reason: the paper identifies g with the one-parameter groups of isometries (p. 7) and T with push-forward by θ ((4.5), p. 8); Reading 1
--   - reading: Ω_{ξ,α} := φ_α⁻¹(Ω₊), asserted to be a subset of Ω₊ that increases to Ω₊ as α → 0⁺ → U_α = {p : φ_s(p) ∈ Ω₊ for all s ∈ [0, α]}; reason: φ_α⁻¹(Ω₊) is not inside Ω₊ (for ∂_t it is {t > −α}), and Ω₊ ∩ φ_α⁻¹(Ω₊) makes the theorem false (rotations of ℝ² at α = 2π); U_α has every property the proof asserts; Reading 2
--   - reading: monomials Φ(f₁)…Φ(f_n) with f_i ∈ S and supp f_i ⊂ Ω → f_i ∈ C_c^∞(M, ℝ) with tsupport f_i ⊆ Ω, n ≥ 0; reason: the elements of S with compact support in Ω; the proof step ⋃E_{Ω_{ξ,α}} = E₊ needs compact supports for a general µ; Reading 3
--   - generalization: a measure µ on S′ with E = L²(S′, µ) and monomials dense → any probability space with a real-linear field Φ whose monomials are in L², and E the closed complex span of the monomials; reason: the paper's case is Φ(f)(ω) = ω(f) on S′, where this E is all of L²(S′, µ); Reading 4
--   - reading: Assumption 2: Γ is a unitary representation of the isometry group G on E → unitaries Θ, Γ(α) of E acting on monomials by (2.2), with α ↦ Γ(α)F continuous; reason: only θ and the flow are used, which assumes less; "unitary representation" is read in its standard, strongly continuous sense, which the proof needs; Reading 5
--   - encoding: (3.1): ∫ conj(Γ(θ)F) F dµ ≥ 0, i.e. (F, F) = ⟨ΘF, F⟩ ≥ 0 → 0 ≤ Re⟪ΘF, F⟫ on E₊, in ReflectionData.positive; reason: ⟪ΘF, F⟫ is real since Θ is a self-adjoint unitary, so the real part loses nothing; Reading 6
--   - generalization: M orientable → no orientation assumed; reason: no step uses an orientation, and orientable M are instances; Reading 8
--   - encoding: Definition 2.1: Killing field ξ orthogonal to Σ with complete orbits meeting Σ once → a flow, a smooth time t with t(φ_s p) = t(p) + s, and ξ ⟂ ker dt on Σ; θ(p) = φ_{−2t(p)}(p); reason: the paper infers t and θ from Definition 2.1 (p. 2); Reading 9
-- source:
--   Jaffe, Ritter, Quantum Field Theory on Curved Backgrounds. II. Spacetime Symmetries, arXiv:0704.0052v1, proof of Theorem 6.4, p. 12

import Mathlib
import Definitions.Def_JRCurvedQFT_Symmetries_trajectorySet
import Definitions.Def_JRCurvedQFT_Symmetries_IsometryFlow
import Definitions.Def_JRCurvedQFT_Symmetries_localSpace
import Definitions.Def_JRCurvedQFT_Symmetries_IsTimeReflection
import Definitions.Def_JRCurvedQFT_Symmetries_IsFlowAction
import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P92

open scoped Manifold ContDiff ENNReal Topology InnerProductSpace
open Bundle MeasureTheory
open QAlgorithms.Papers.Independent.Intakethird100.P92

namespace JRCurvedQFT.Symmetries

/-- **The quantization of a reflected flow on `𝒟_{ξ,α}`.** If the isometries are reflected, then for every
`α ≥ 0`: (a) `Γ(φ_α)` maps `E_{U_α}` into `E₊`; (b) `Π(F) = 0` implies `Π(Γ(φ_α)F) = 0` for `F ∈ E_{U_α}`, so
`Γ(φ_α)` has a well-defined quantization on `𝒟_{ξ,α} = Π(E_{U_α})`; (c) that quantization is symmetric.

Jaffe, Ritter, *Quantum Field Theory on Curved Backgrounds. II. Spacetime Symmetries*, arXiv:0704.0052v1, proof of Theorem 6.4, p. 12: "Since φ_α(Ω_{ξ,α}) ⊆ Ω₊, we infer that Γ(φ_α)E_{Ω_{ξ,α}} ⊆ E₊. By
Theorem 3.5, Γ(φ_α) has a quantization which is a symmetric operator on the domain
𝒟_{ξ,α} := Π(E_{Ω_{ξ,α}})."

**Formalization Note** `Ω_{ξ,α}` is read as `U_α` (see `trajectorySet`). The claim is the paper's, but
its appeal to Theorem 3.5 does not apply: QC-II(iii) needs `T⁺T = Γ(φ_{2α})` to map `E_{U_α}` into `E₊`,
which fails for the rotation wedge of `ℝ²` (`U_α` = angles `(0, π − α)`, `φ_{2α}(U_α)` = angles
`(2α, π + α)`). Theorem 3.5 is not a milestone. -/
theorem reflected_quantization {d : ℕ} {M : Type} [EMetricSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin d)) M] [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin d)) ∞ M]
    [RiemannianBundle (fun (x : M) ↦ TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin d)) x)]
    [IsContMDiffRiemannianBundle 𝓘(ℝ, EuclideanSpace ℝ (Fin d)) ∞ (EuclideanSpace ℝ (Fin d))
      (fun (x : M) ↦ TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin d)) x)]
    [IsRiemannianManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin d)) M] [CompleteSpace M] [ConnectedSpace M]
    (S : JRCurvedQFT.SharpTime.StaticStructure (d := d) M) (φ : IsometryFlow (d := d) M)
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    (Φ : EuclideanField (d := d) M P) (r : ReflectionData (fieldSpace Φ))
    (hr : IsTimeReflection S Φ r)
    (Γ : ℝ → (fieldSpace Φ ≃ₗᵢ[ℂ] fieldSpace Φ)) (hΓ : IsFlowAction φ Φ Γ)
    (hφ : IsometryFlow.IsReflected S φ) (α : ℝ) (hα : 0 ≤ α) :
    (∀ F ∈ localSpace Φ (trajectorySet S φ α), Γ α F ∈ r.plus) ∧
    (∀ F : r.plus, (F : fieldSpace Φ) ∈ localSpace Φ (trajectorySet S φ α) →
      ∀ hF : Γ α F ∈ r.plus, osQ r F = 0 → osQ r ⟨Γ α F, hF⟩ = 0) ∧
    (∀ F G : r.plus, (F : fieldSpace Φ) ∈ localSpace Φ (trajectorySet S φ α) →
      (G : fieldSpace Φ) ∈ localSpace Φ (trajectorySet S φ α) →
      ∀ (hF : Γ α F ∈ r.plus) (hG : Γ α G ∈ r.plus),
        ⟪osQ r G, osQ r ⟨Γ α F, hF⟩⟫_ℂ = ⟪osQ r ⟨Γ α G, hG⟩, osQ r F⟫_ℂ) := by sorry

end JRCurvedQFT.Symmetries
