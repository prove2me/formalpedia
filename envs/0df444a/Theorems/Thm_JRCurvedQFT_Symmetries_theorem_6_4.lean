-- Prove2me | Theorems.Thm_JRCurvedQFT_Symmetries_theorem_6_4
-- name    : JRCurvedQFT.Symmetries.theorem_6_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-04T07:07:20.647894+00:00
-- url     : https://prove2.me/theorems/7a598275-0dfe-4453-94cf-8bc52439d112
-- title:
--   Theorem 6.4 — $\widehat\Gamma(\phi_\alpha)=e^{-\alpha A_\xi}$ for $\xi\in\mathfrak g_-$ and $e^{i\alpha A_\xi}$ for $\xi\in\mathfrak g_+$, with $A_\xi$ self-adjoint
-- statement:
--   Throughout, $M$ is a quantizable static space-time: a complete connected smooth Riemannian manifold with a static flow $\phi^0_s$ of isometries, a smooth time $t$ with $t(\phi^0_s p)=t(p)+s$, the slice $\Sigma=\{t=0\}$, the regions $\Omega_\pm=\{\pm t>0\}$ and the time reflection $\theta$. $\Phi$ is a real-linear field on the test functions $C_c^\infty(M,\mathbb R)$ over a probability space, with every monomial $\Phi(f_1)\cdots\Phi(f_n)$ in $L^2$; $\mathcal E$ is the closed complex span of the monomials, and $\mathcal E_U$ the closed span of those with $\operatorname{supp}f_i\subset U$, with $\mathcal E_+=\mathcal E_{\Omega_+}$. $\Theta$ is a unitary of $\mathcal E$ with $\Theta\prod\Phi(f_i)=\prod\Phi(f_i\circ\theta)$ and $\operatorname{Re}\langle\Theta F,F\rangle\ge0$ on $\mathcal E_+$ (Assumption 1); $\mathcal H$ is the completion of $\mathcal E_+/\mathcal N$ for $\langle\hat A,\hat B\rangle=\langle\Theta A,B\rangle$, and $\Pi(A)=\hat A$. $\{\phi_\alpha\}$ is a one-parameter group of isometries and $\Gamma(\alpha)$ a strongly continuous family of unitaries of $\mathcal E$ with $\Gamma(\alpha)\prod\Phi(f_i)=\prod\Phi(f_i\circ\phi_{-\alpha})$ (Assumption 2). The flow is **reflected** ($\xi\in\mathfrak g_-$) if $\theta\phi_\alpha\theta=\phi_{-\alpha}$, and **reflection-invariant** ($\xi\in\mathfrak g_+$) if $\theta\phi_\alpha\theta=\phi_\alpha$. $U_\alpha=\{p:\phi_s(p)\in\Omega_+\ \forall s\in[0,\alpha]\}$.
--
--   Then each of the following holds.
--
--   1. If the flow is reflected, there is a densely defined self-adjoint operator $A$ on $\mathcal H$ such that for every $\alpha\ge0$ and $F\in\mathcal E_{U_\alpha}$: $F$ and $\Gamma(\alpha)F$ lie in $\mathcal E_+$, $\Pi(F)\in D(e^{-\alpha A})$, and
--   $$e^{-\alpha A}\Pi(F)=\Pi(\Gamma(\alpha)F).$$
--   2. If the flow is reflection-invariant, there is a densely defined self-adjoint operator $A$ on $\mathcal H$ such that for every $\alpha\in\mathbb R$ and $F\in\mathcal E_+$: $\Gamma(\alpha)F\in\mathcal E_+$, $\Pi(F)\in D(e^{i\alpha A})$, and
--   $$e^{i\alpha A}\Pi(F)=\Pi(\Gamma(\alpha)F).$$
--
--   The theorem attaches a self-adjoint generator on the Hilbert space of quantum theory to each Killing field in $\mathfrak g_\pm$. Analytic continuation (§7 of the paper) reads the generators of $\mathfrak g_-$ as the boosts of the Lorentzian space-time.
--
--   Differences from the source:
--   - generalization: the proof gets Γ̂(φ_α) = exp(−αA_ξ) for all α ∈ [0, a] → every α ≥ 0, with the domain Π(E_{U_α}) for each α; reason: U_α makes every α ≥ 0 meaningful, and α ∈ [0, a] is a special case; Theorem 6.4 as printed gives no range
--   - reading: Γ̂(φ_α) = e^{−αA_ξ}, as operators → an equality on Π(E_{U_α}), with Π(F) ∈ D(e^{−αA}), and on Π(E₊) in the g₊ case; reason: Γ̂(φ_α) is defined only on these domains, which the proof makes explicit (Definition 6.1, Theorem 6.2)
--   - encoding: a Killing field ξ ∈ g∓ with its one-parameter group {φ_α} → a jointly smooth one-parameter group of isometries φ with θφ_αθ = φ_{∓α}; reason: the paper identifies g with the one-parameter groups of isometries (p. 7) and T with push-forward by θ ((4.5), p. 8); Reading 1
--   - reading: Ω_{ξ,α} := φ_α⁻¹(Ω₊), asserted to be a subset of Ω₊ that increases to Ω₊ as α → 0⁺ → U_α = {p : φ_s(p) ∈ Ω₊ for all s ∈ [0, α]}; reason: φ_α⁻¹(Ω₊) is not inside Ω₊ (for ∂_t it is {t > −α}), and Ω₊ ∩ φ_α⁻¹(Ω₊) makes the theorem false (rotations of ℝ² at α = 2π); U_α has every property the proof asserts; Reading 2
--   - reading: monomials Φ(f₁)…Φ(f_n) with f_i ∈ S and supp f_i ⊂ Ω → f_i ∈ C_c^∞(M, ℝ) with tsupport f_i ⊆ Ω, n ≥ 0; reason: the elements of S with compact support in Ω; the proof step ⋃E_{Ω_{ξ,α}} = E₊ needs compact supports for a general µ; Reading 3
--   - generalization: a measure µ on S′ with E = L²(S′, µ) and monomials dense → any probability space with a real-linear field Φ whose monomials are in L², and E the closed complex span of the monomials; reason: the paper's case is Φ(f)(ω) = ω(f) on S′, where this E is all of L²(S′, µ); Reading 4
--   - reading: Assumption 2: Γ is a unitary representation of the isometry group G on E → unitaries Θ, Γ(α) of E acting on monomials by (2.2), with α ↦ Γ(α)F continuous; reason: only θ and the flow are used, which assumes less; "unitary representation" is read in its standard, strongly continuous sense, which the proof needs; Reading 5
--   - encoding: (3.1): ∫ conj(Γ(θ)F) F dµ ≥ 0, i.e. (F, F) = ⟨ΘF, F⟩ ≥ 0 → 0 ≤ Re⟪ΘF, F⟫ on E₊, in ReflectionData.positive; reason: ⟪ΘF, F⟫ is real since Θ is a self-adjoint unitary, so the real part loses nothing; Reading 6
--   - encoding: e^{−αA}, e^{iαA} → the spectral integrals ∫e^{−αx}dQ(x), ∫e^{iαx}dQ(x) of the projection-valued measure Q with A = ∫x dQ(x); reason: the standard functional calculus; every self-adjoint A has such a Q; Reading 7
--   - generalization: M orientable → no orientation assumed; reason: no step uses an orientation, and orientable M are instances; Reading 8
--   - encoding: Definition 2.1: Killing field ξ orthogonal to Σ with complete orbits meeting Σ once → a flow, a smooth time t with t(φ_s p) = t(p) + s, and ξ ⟂ ker dt on Σ; θ(p) = φ_{−2t(p)}(p); reason: the paper infers t and θ from Definition 2.1 (p. 2); Reading 9
-- source:
--   Jaffe, Ritter, Quantum Field Theory on Curved Backgrounds. II. Spacetime Symmetries, arXiv:0704.0052v1, Theorem 6.4, p. 11; proof, p. 12

import Mathlib
import Definitions.Def_JRCurvedQFT_Symmetries_trajectorySet
import Definitions.Def_JRCurvedQFT_Symmetries_IsometryFlow
import Definitions.Def_JRCurvedQFT_Symmetries_localSpace
import Definitions.Def_JRCurvedQFT_Symmetries_IsTimeReflection
import Definitions.Def_JRCurvedQFT_Symmetries_IsFlowAction
import Definitions.Def_JRCurvedQFT_Symmetries_IsSpectralGenerator
import Definitions.Def_JRCurvedQFT_Symmetries_spectralExpNeg
import Definitions.Def_JRCurvedQFT_Symmetries_spectralExpI
import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P92

open scoped Manifold ContDiff ENNReal Topology InnerProductSpace
open Bundle MeasureTheory
open QAlgorithms.Papers.Independent.Intakethird100.P92

namespace JRCurvedQFT.Symmetries

/-- **Theorem 6.4.** Let `M` be a quantizable static space-time, `Φ` a field satisfying Assumptions 1–2, and
`φ` the one-parameter group of isometries of a Killing field `ξ` that lies in `g₋` or `g₊`. Then there is a
densely defined self-adjoint operator `A` on `ℋ` with `Γ̂(φ_α) = e^{−αA}` if `ξ ∈ g₋`, and `Γ̂(φ_α) = e^{iαA}` if
`ξ ∈ g₊`. Precisely:

* (`ξ ∈ g₋`) for every `α ≥ 0` and `F ∈ E_{U_α}`: `F` and `Γ(φ_α)F` lie in `E₊`, `Π(F) ∈ D(e^{−αA})`, and
  `e^{−αA} Π(F) = Π(Γ(φ_α)F)`;
* (`ξ ∈ g₊`) for every `α ∈ ℝ` and `F ∈ E₊`: `Γ(φ_α)F ∈ E₊`, `Π(F) ∈ D(e^{iαA})`, and
  `e^{iαA} Π(F) = Π(Γ(φ_α)F)`.

Jaffe, Ritter, *Quantum Field Theory on Curved Backgrounds. II. Spacetime Symmetries*, arXiv:0704.0052v1, Theorem 6.4, p. 11; proof, p. 12.

**Formalization Note** `Ω_{ξ,α}` is read as `U_α` (`trajectorySet`). The proof fixes `a` and gets
`α ∈ [0, a]`; the statement here covers every `α ≥ 0`, which is stronger. The operator `A` of the two
cases is existential in each case separately, as `A_ξ` depends on `ξ`. The exponentials are spectral
integrals of the projection-valued measure `Q` of `A`. -/
theorem theorem_6_4 {d : ℕ} {M : Type} [EMetricSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin d)) M] [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin d)) ∞ M]
    [RiemannianBundle (fun (x : M) ↦ TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin d)) x)]
    [IsContMDiffRiemannianBundle 𝓘(ℝ, EuclideanSpace ℝ (Fin d)) ∞ (EuclideanSpace ℝ (Fin d))
      (fun (x : M) ↦ TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin d)) x)]
    [IsRiemannianManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin d)) M] [CompleteSpace M] [ConnectedSpace M]
    (S : JRCurvedQFT.SharpTime.StaticStructure (d := d) M) (φ : IsometryFlow (d := d) M)
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    (Φ : EuclideanField (d := d) M P) (r : ReflectionData (fieldSpace Φ))
    (hr : IsTimeReflection S Φ r)
    (Γ : ℝ → (fieldSpace Φ ≃ₗᵢ[ℂ] fieldSpace Φ)) (hΓ : IsFlowAction φ Φ Γ) :
    (IsometryFlow.IsReflected S φ →
      ∃ A : OS r →ₗ.[ℂ] OS r, Dense (A.domain : Set (OS r)) ∧ IsSelfAdjoint A ∧
        ∃ Q : Set ℝ → (OS r →L[ℂ] OS r), IsSpectralGenerator Q A ∧
          ∀ α : ℝ, 0 ≤ α → ∀ F ∈ localSpace Φ (trajectorySet S φ α),
            ∃ (hF : F ∈ r.plus) (hΓF : Γ α F ∈ r.plus)
              (hd : osQ r ⟨F, hF⟩ ∈ (spectralExpNeg Q α).domain),
              spectralExpNeg Q α ⟨osQ r ⟨F, hF⟩, hd⟩ = osQ r ⟨Γ α F, hΓF⟩) ∧
    (IsometryFlow.IsReflectionInvariant S φ →
      ∃ A : OS r →ₗ.[ℂ] OS r, Dense (A.domain : Set (OS r)) ∧ IsSelfAdjoint A ∧
        ∃ Q : Set ℝ → (OS r →L[ℂ] OS r), IsSpectralGenerator Q A ∧
          ∀ (α : ℝ) (F : r.plus),
            ∃ (hΓF : Γ α F ∈ r.plus) (hd : osQ r F ∈ (spectralExpI Q α).domain),
              spectralExpI Q α ⟨osQ r F, hd⟩ = osQ r ⟨Γ α F, hΓF⟩) := by sorry

end JRCurvedQFT.Symmetries
