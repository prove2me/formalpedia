-- Prove2me | Theorems.Thm_JRCurvedQFT_SharpTime_sharpTime_approximation
-- name    : JRCurvedQFT.SharpTime.sharpTime_approximation
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T18:39:10.955034+00:00
-- url     : https://prove2.me/theorems/846e155c-3dae-4fab-9be9-b0e2af083854
-- title:
--   Proof of Theorem 4.4, p. 25 — sharp-time distributions $f_t$ ($t>0$) are $H_{-1}$-limits of positive-time test functions, and $f_t\to f_0$
-- statement:
--   Throughout, $M$ is a quantizable static spacetime (Definition 4.1): a complete, connected, smooth Riemannian manifold of dimension $d$ with a global static Killing flow $\phi_s$ (each $\phi_s$ an isometry), a smooth time function $t$ with $t(\phi_s p)=t(p)+s$, the time-zero slice $\Sigma=\{t=0\}$ orthogonal to the Killing field $\xi$, the regions $\Omega_\pm=\{\pm t>0\}$, the reflection $\theta$ and the lapse $F=\langle\xi,\xi\rangle$; $\mathrm{dvol}$ is its Riemannian volume.
--
--   Let $m>0$ and let $f\in C_c^\infty(\Sigma)$ be real. Then:
--
--   1. for every $t\ge0$, the sharp-time distribution $f_t$ lies in $H_{-1}(M)$;
--   2. for every $t>0$ there are smooth test functions $g_n$ with compact support in $\Omega_+$ with $g_n\to f_t$ in $H_{-1}(M)$ (for every $\varepsilon>0$ some $g$ has $\|g-f_t\|_{-1}<\varepsilon$);
--   3. $\|f_t-f_0\|_{-1}\to0$ as $t\to0^+$.
--
--   With the continuity of $h\mapsto e^{i\Phi(h)}$ this gives $\exp(i\Phi(f_t))\in\mathcal E_+$ for $t>0$ and, in the limit, $\exp(i\Phi(f_0))\in\mathcal E_+$.
--
--   Differences from the source:
--   - reading: the class of f is not specified (the proof writes g ∈ 𝒯_Σ, never defined) → real f ∈ C_c^∞(Σ), encoded by smooth ξ-invariant lifts f : M → ℝ with Σ ∩ tsupport f compact; reason: smallest natural class; it makes density hardest and isometry/membership extend to closures (Reading 2)
--   - encoding: quantizable static spacetime (Definition 4.1) with Example 1.1 → complete connected Riemannian manifold with a global isometric flow φ_s and a smooth time function with t∘φ_s = t + s and ξ ⟂ ker dt on Σ = {t = 0}; reason: equivalent to Definition 4.1 with the uniqueness of t that Example 1.1 needs (Reading 3)
--   - encoding: H₋₁(M) as the completion of C^∞(M) in ⟨f, Cf⟩, ⟨f, Cg⟩ with C = (−Δ+m²)⁻¹, and dvol → ‖ℓ‖₋₁ = sup of |ℓ(u)| over u ∈ C_c^∞(M) with ∫(|∇u|²+m²u²) dvol ≤ 1, ⟨·, C·⟩ by polarization, dvol characterized by its chart densities √det g; reason: on a complete M, −Δ is essentially self-adjoint on C_c^∞ and this dual norm is ⟨f, Cf⟩^{1/2}; same objects (Reading 4)
--   - encoding: the paper presupposes f_t ∈ H₋₁(M) → conclusion 1 states f_t ∈ H₋₁(M) for t ≥ 0; reason: the sharp-time distribution is not an element of H₋₁(M) by construction
--   - reading: "By taking the t → 0 limit" → f_t → f₀ in H₋₁(M) as t → 0⁺; reason: the limit is taken in the Sobolev topology of the preceding sentence
-- source:
--   Jaffe, Ritter, Quantum Field Theory on Curved Backgrounds. I. The Euclidean Functional Integral, arXiv:hep-th/0609003v1, proof of Theorem 4.4, p. 25

import Mathlib
import Definitions.Def_JRCurvedQFT_SharpTime_IsRiemannianVolume
import Definitions.Def_JRCurvedQFT_SharpTime_sharpTime
import Definitions.Def_JRCurvedQFT_SharpTime_IsHminus1
import Definitions.Def_JRCurvedQFT_SharpTime_ofFunction
import Definitions.Def_JRCurvedQFT_SharpTime_IsSliceTestFunction

open scoped Manifold ContDiff ENNReal Topology
open Bundle MeasureTheory

namespace JRCurvedQFT.SharpTime

/-- **Proof of Theorem 4.4, p. 25.** Sharp-time distributions are `H₋₁`-limits of positive-time test
functions, and `f_t → f₀` as `t → 0⁺`.

Jaffe, Ritter, *Quantum Field Theory on Curved Backgrounds. I. The Euclidean Functional Integral*, arXiv:hep-th/0609003v1, proof of Theorem 4.4, p. 25: "If t > 0, then there exists a sequence of smooth test functions
{g_n} with compact, positive-time support such that lim_{n→∞} g_n = f_t in the Sobolev topology,
hence exp(iΦ(f_t)) ∈ ℰ₊. ... By taking the t → 0 limit, we see that exp(iΦ(f₀)) ∈ ℰ₊".

Setting (Definition 4.1): `M` is a complete, connected, smooth Riemannian manifold of dimension
`d` (charts in `ℝ^d`, smooth metric, distance = Riemannian distance) with a static structure `S`
(flow `φ_s` of the static Killing field, time function `t`, slice `Σ = {t = 0}`), and `μ` is its
Riemannian volume. `m > 0`; `f` is a real test function on `Σ`. Conclusions:
1. for every `t ≥ 0`, `f_t ∈ H₋₁(M)`;
2. for every `t > 0` and `ε > 0` there is `g ∈ C_c^∞(M)` with `tsupport g ⊆ Ω₊` and `‖g − f_t‖₋₁ < ε`;
3. `‖f_t − f₀‖₋₁ → 0` as `t → 0⁺`.

**Formalization Note** "Sobolev topology" is the `H₋₁(M)` norm (Reading 4). -/
theorem sharpTime_approximation {d : ℕ} {M : Type} [EMetricSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin d)) M] [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin d)) ∞ M]
    [RiemannianBundle (fun (x : M) ↦ TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin d)) x)]
    [IsContMDiffRiemannianBundle 𝓘(ℝ, EuclideanSpace ℝ (Fin d)) ∞ (EuclideanSpace ℝ (Fin d))
      (fun (x : M) ↦ TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin d)) x)]
    [IsRiemannianManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin d)) M] [CompleteSpace M] [ConnectedSpace M]
    [MeasurableSpace M] [BorelSpace M]
    (S : StaticStructure (d := d) M) (μ : Measure M) (hμ : IsRiemannianVolume (d := d) μ)
    (m : ℝ) (hm : 0 < m) (f : M → ℝ) (hf : IsSliceTestFunction S f) :
    (∀ t : ℝ, 0 ≤ t → IsHminus1 (d := d) μ m (sharpTime S μ f t)) ∧
    (∀ t : ℝ, 0 < t → ∀ ε : ℝ≥0∞, 0 < ε → ∃ g : M → ℝ, IsTestFunction (d := d) g ∧
      tsupport g ⊆ S.positiveTime ∧
      negSobolevNorm (d := d) μ m (ofFunction μ g - sharpTime S μ f t) < ε) ∧
    Filter.Tendsto (fun t => negSobolevNorm (d := d) μ m (sharpTime S μ f t - sharpTime S μ f 0))
      (𝓝[>] 0) (𝓝 0) := by sorry

end JRCurvedQFT.SharpTime
