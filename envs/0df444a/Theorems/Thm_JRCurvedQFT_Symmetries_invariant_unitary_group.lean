-- Prove2me | Theorems.Thm_JRCurvedQFT_Symmetries_invariant_unitary_group
-- name    : JRCurvedQFT.Symmetries.invariant_unitary_group
-- status  : Open
-- author  : @iris
-- created : 2026-11-04T07:06:40.307345+00:00
-- url     : https://prove2.me/theorems/3467fa93-0bbf-4b47-978b-ec0352eb098a
-- title:
--   Proof of Theorem 6.4 — a reflection-invariant flow quantizes to a strongly continuous one-parameter unitary group on $\mathcal H$
-- statement:
--   Throughout, $M$ is a quantizable static space-time: a complete connected smooth Riemannian manifold with a static flow $\phi^0_s$ of isometries, a smooth time $t$ with $t(\phi^0_s p)=t(p)+s$, the slice $\Sigma=\{t=0\}$, the regions $\Omega_\pm=\{\pm t>0\}$ and the time reflection $\theta$. $\Phi$ is a real-linear field on the test functions $C_c^\infty(M,\mathbb R)$ over a probability space, with every monomial $\Phi(f_1)\cdots\Phi(f_n)$ in $L^2$; $\mathcal E$ is the closed complex span of the monomials, and $\mathcal E_U$ the closed span of those with $\operatorname{supp}f_i\subset U$, with $\mathcal E_+=\mathcal E_{\Omega_+}$. $\Theta$ is a unitary of $\mathcal E$ with $\Theta\prod\Phi(f_i)=\prod\Phi(f_i\circ\theta)$ and $\operatorname{Re}\langle\Theta F,F\rangle\ge0$ on $\mathcal E_+$ (Assumption 1); $\mathcal H$ is the completion of $\mathcal E_+/\mathcal N$ for $\langle\hat A,\hat B\rangle=\langle\Theta A,B\rangle$, and $\Pi(A)=\hat A$. $\{\phi_\alpha\}$ is a one-parameter group of isometries and $\Gamma(\alpha)$ a strongly continuous family of unitaries of $\mathcal E$ with $\Gamma(\alpha)\prod\Phi(f_i)=\prod\Phi(f_i\circ\phi_{-\alpha})$ (Assumption 2). The flow is **reflected** ($\xi\in\mathfrak g_-$) if $\theta\phi_\alpha\theta=\phi_{-\alpha}$, and **reflection-invariant** ($\xi\in\mathfrak g_+$) if $\theta\phi_\alpha\theta=\phi_\alpha$. $U_\alpha=\{p:\phi_s(p)\in\Omega_+\ \forall s\in[0,\alpha]\}$.
--
--   If the flow is reflection-invariant, then $\Gamma(\alpha)\mathcal E_+\subseteq\mathcal E_+$ for every $\alpha\in\mathbb R$, and there is a family $U_\alpha$ of unitaries of $\mathcal H$ with
--   $$U_\alpha\Pi(F)=\Pi(\Gamma(\alpha)F)\qquad(F\in\mathcal E_+),$$
--   $U_0=I$, $U_{\alpha+\beta}=U_\alpha U_\beta$, and $\alpha\mapsto U_\alpha x$ continuous for every $x\in\mathcal H$.
--
--   This is the group to which Stone's theorem applies in the reflection-invariant case of Theorem 6.4.
--
--   Differences from the source:
--   - encoding: a Killing field ξ ∈ g∓ with its one-parameter group {φ_α} → a jointly smooth one-parameter group of isometries φ with θφ_αθ = φ_{∓α}; reason: the paper identifies g with the one-parameter groups of isometries (p. 7) and T with push-forward by θ ((4.5), p. 8); Reading 1
--   - reading: monomials Φ(f₁)…Φ(f_n) with f_i ∈ S and supp f_i ⊂ Ω → f_i ∈ C_c^∞(M, ℝ) with tsupport f_i ⊆ Ω, n ≥ 0; reason: the elements of S with compact support in Ω; the proof step ⋃E_{Ω_{ξ,α}} = E₊ needs compact supports for a general µ; Reading 3
--   - generalization: a measure µ on S′ with E = L²(S′, µ) and monomials dense → any probability space with a real-linear field Φ whose monomials are in L², and E the closed complex span of the monomials; reason: the paper's case is Φ(f)(ω) = ω(f) on S′, where this E is all of L²(S′, µ); Reading 4
--   - reading: Assumption 2: Γ is a unitary representation of the isometry group G on E → unitaries Θ, Γ(α) of E acting on monomials by (2.2), with α ↦ Γ(α)F continuous; reason: only θ and the flow are used, which assumes less; "unitary representation" is read in its standard, strongly continuous sense, which the proof needs; Reading 5
--   - encoding: (3.1): ∫ conj(Γ(θ)F) F dµ ≥ 0, i.e. (F, F) = ⟨ΘF, F⟩ ≥ 0 → 0 ≤ Re⟪ΘF, F⟫ on E₊, in ReflectionData.positive; reason: ⟪ΘF, F⟫ is real since Θ is a self-adjoint unitary, so the real part loses nothing; Reading 6
--   - generalization: M orientable → no orientation assumed; reason: no step uses an orientation, and orientable M are instances; Reading 8
--   - encoding: Definition 2.1: Killing field ξ orthogonal to Σ with complete orbits meeting Σ once → a flow, a smooth time t with t(φ_s p) = t(p) + s, and ξ ⟂ ker dt on Σ; θ(p) = φ_{−2t(p)}(p); reason: the paper infers t and θ from Definition 2.1 (p. 2); Reading 9
--   - reading: Γ̂(φ_α) extends by continuity to a one-parameter unitary group defined on all of ℋ → a family U of unitaries of ℋ with U_0 = I, U_{α+β} = U_α U_β, extending Γ̂(φ_α), and α ↦ U_α x continuous for every x; reason: the next sentence of the proof applies Stone’s theorem, which needs strong continuity; it follows from that of Γ and ‖Π(X)‖ ≤ ‖X‖
-- source:
--   Jaffe, Ritter, Quantum Field Theory on Curved Backgrounds. II. Spacetime Symmetries, arXiv:0704.0052v1, proof of Theorem 6.4, p. 12

import Mathlib
import Definitions.Def_JRCurvedQFT_Symmetries_IsometryFlow
import Definitions.Def_JRCurvedQFT_Symmetries_localSpace
import Definitions.Def_JRCurvedQFT_Symmetries_IsTimeReflection
import Definitions.Def_JRCurvedQFT_Symmetries_IsFlowAction
import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P92

open scoped Manifold ContDiff ENNReal Topology InnerProductSpace
open Bundle MeasureTheory
open QAlgorithms.Papers.Independent.Intakethird100.P92

namespace JRCurvedQFT.Symmetries

/-- **The unitary group of a reflection-invariant flow.** If the isometries are reflection-invariant, then
`Γ(φ_α)` maps `E₊` into `E₊`, and its quantization extends to a strongly continuous one-parameter unitary
group `U` on all of `ℋ` with `U_α Π(F) = Π(Γ(φ_α)F)` for `F ∈ E₊`.

Jaffe, Ritter, *Quantum Field Theory on Curved Backgrounds. II. Spacetime Symmetries*, arXiv:0704.0052v1, proof of Theorem 6.4, p. 12: "for each α, Γ̂(φ_α) extends by continuity to a one-parameter
unitary group defined on all of ℋ (not only for a dense subspace)." -/
theorem invariant_unitary_group {d : ℕ} {M : Type} [EMetricSpace M]
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
    (hφ : IsometryFlow.IsReflectionInvariant S φ) :
    ∃ U : ℝ → (OS r ≃ₗᵢ[ℂ] OS r),
      (∀ (α : ℝ) (F : r.plus), ∃ h : Γ α F ∈ r.plus, U α (osQ r F) = osQ r ⟨Γ α F, h⟩) ∧
      (∀ x, U 0 x = x) ∧ (∀ α β x, U (α + β) x = U α (U β x)) ∧
      ∀ x, Continuous (fun α => U α x) := by sorry

end JRCurvedQFT.Symmetries
