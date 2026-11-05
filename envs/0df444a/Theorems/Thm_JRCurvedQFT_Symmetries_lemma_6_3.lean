-- Prove2me | Theorems.Thm_JRCurvedQFT_Symmetries_lemma_6_3
-- name    : JRCurvedQFT.Symmetries.lemma_6_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-04T07:01:16.151256+00:00
-- url     : https://prove2.me/theorems/670cd42d-2564-4d63-acec-5b1262b66a7d
-- title:
--   Lemma 6.3 — a reflection-invariant isometry that keeps one point of $\Omega_+$ in $\Omega_+$ preserves $\Omega_+$
-- statement:
--   Let $M$ be a quantizable static space-time with time reflection $\theta$ and positive-time region $\Omega_+$. Let $\psi$ be a bijective isometry of $M$ which is reflection-invariant, $\theta\psi\theta=\psi$, and assume there is $p\in\Omega_+$ with $\psi(p)\in\Omega_+$. Then
--   $$\psi(\Omega_+)\subseteq\Omega_+.$$
--   This shows that the flow of a Killing field in $\mathfrak g_+$ leaves the positive-time region invariant, and so its unitaries preserve $\mathcal E_+$.
--
--   Differences from the source:
--   - generalization: M orientable → no orientation assumed; reason: no step uses an orientation, and orientable M are instances; Reading 8
--   - encoding: Definition 2.1: Killing field ξ orthogonal to Σ with complete orbits meeting Σ once → a flow, a smooth time t with t(φ_s p) = t(p) + s, and ξ ⟂ ker dt on Σ; θ(p) = φ_{−2t(p)}(p); reason: the paper infers t and θ from Definition 2.1 (p. 2); Reading 9
--   - encoding: ψ an isometry of the Riemannian manifold (M, g_ab), an element of Iso(M) → ψ : M ≃ᵢ M, a bijective isometry of the Riemannian distance of M (IsRiemannianManifold); reason: by Myers–Steenrod the distance-preserving bijections of a connected Riemannian manifold are exactly its Riemannian isometries
-- source:
--   Jaffe, Ritter, Quantum Field Theory on Curved Backgrounds. II. Spacetime Symmetries, arXiv:0704.0052v1, Lemma 6.3, p. 11

import Mathlib
import Definitions.Def_JRCurvedQFT_SharpTime_StaticStructure

open scoped Manifold ContDiff ENNReal Topology InnerProductSpace
open Bundle MeasureTheory

namespace JRCurvedQFT.Symmetries

/-- **Lemma 6.3.** A reflection-invariant isometry that maps one point of `Ω₊` into `Ω₊` maps `Ω₊` into
`Ω₊`.

Jaffe, Ritter, *Quantum Field Theory on Curved Backgrounds. II. Spacetime Symmetries*, arXiv:0704.0052v1, Lemma 6.3, p. 11: "Let ψ be a reflection-invariant isometry and assume ∃ p ∈ Ω₊ such that
ψ(p) ∈ Ω₊. Then ψ preserves the positive-time subspace, i.e. ψ(Ω₊) ⊆ Ω₊."

**Formalization Note** `ψ` is any bijective isometry of the metric space `M`, and
reflection-invariant means `θ ψ θ = ψ` (Definition 5.1, p. 9). -/
theorem lemma_6_3 {d : ℕ} {M : Type} [EMetricSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin d)) M] [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin d)) ∞ M]
    [RiemannianBundle (fun (x : M) ↦ TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin d)) x)]
    [IsContMDiffRiemannianBundle 𝓘(ℝ, EuclideanSpace ℝ (Fin d)) ∞ (EuclideanSpace ℝ (Fin d))
      (fun (x : M) ↦ TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin d)) x)]
    [IsRiemannianManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin d)) M] [CompleteSpace M] [ConnectedSpace M]
    (S : JRCurvedQFT.SharpTime.StaticStructure (d := d) M) (ψ : M ≃ᵢ M)
    (hψ : ∀ p, S.reflection (ψ (S.reflection p)) = ψ p)
    (hp : ∃ p ∈ S.positiveTime, ψ p ∈ S.positiveTime) :
    ψ '' S.positiveTime ⊆ S.positiveTime := by sorry

end JRCurvedQFT.Symmetries
