-- Prove2me | Theorems.Thm_HardCoreBochner_theorem_1_2_display
-- name    : HardCoreBochner.theorem_1_2_display
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T17:32:21.281922+00:00
-- url     : https://prove2.me/theorems/95b4197b-0db6-4e7a-8c14-52fb6129061b
-- title:
--   Proof of Theorem 1.2 — $\langle Lf,Lf\rangle_\mu+\delta\langle f,Lf\rangle_\mu\ge\mathbb E_\mu[\psi_\sigma^{\top}M_\sigma\psi_\sigma]\ge0$
-- statement:
--   Let $\mu$ be a distribution fully supported on a non-empty downward-closed family $X\subseteq\{0,1\}^V$, let $\delta\in(0,1)$, and assume that $M_\sigma$ is positive semidefinite for every $\sigma\in X$. For $f:\{0,1\}^V\to\mathbb R$ write $\psi_\sigma(v)=D^+_vf(\sigma)$. Then:
--
--   1. $$\langle Lf,Lf\rangle_\mu+\delta\langle f,Lf\rangle_\mu\ \ge\ \mathbb E_\mu\Big[\sum_{u,v\in V}\big((1-\delta)r_v(\sigma)\mathbf 1_{\{u=v\}}-r_v(\sigma)(D^+_vr_u)(\sigma)\big)\psi_\sigma(u)\psi_\sigma(v)\Big];$$
--   2. $$\langle Lf,Lf\rangle_\mu+\delta\langle f,Lf\rangle_\mu\ \ge\ 0.$$
--
--   The matrix inside the expectation in (1) is $M_\sigma$ from (3), and (2) is the inequality from which the spectral gap follows.
--
--   Differences from the source:
--   - encoding: a distribution µ fully supported on a non-empty downward-closed family X ⊆ {0,1}^V → IsDownClosedLaw µ for µ : (V → Bool) → ℝ, with X := {σ | 0 < µ σ}; reason: the support of such a µ is exactly such an X, and every such pair (X, µ) arises this way; same instances
--   - encoding: M_σ positive semidefinite → 0 ≤ x ⬝ᵥ M_σ *ᵥ x for every x : V → ℝ; reason: this is the quadratic-form meaning of positive semidefinite; M_σ is symmetric on X, so it equals PosSemidef there
--   - encoding: Σ_{u,v∈V} M_σ(u,v) ψ_σ(u) ψ_σ(v) → ψ_σ ⬝ᵥ (M_σ *ᵥ ψ_σ); reason: the same double sum written as a quadratic form
-- source:
--   Göbel, Jenssen, Michelen, Pappik, Perkins, Schiller, A simple proof of rapid mixing on random regular graphs beyond uniqueness, arXiv:2606.27545 (version of 2026-11-03, sha256 dfc58c3b6107de9702dda27883f2839093b816f7a6f9c543fcb2be0ad91ad6ad), proof of Theorem 1.2, pp.8–9 (PDF pp.8–9)

import Definitions.Def_HardCoreBochner_IsDownClosedLaw
import Definitions.Def_HardCoreBochner_gen
import Definitions.Def_HardCoreBochner_ip
import Definitions.Def_HardCoreBochner_Mmat

namespace HardCoreBochner

open scoped BigOperators
open Matrix

/-- **The two displays of the proof of Theorem 1.2.** Göbel, Jenssen, Michelen, Pappik, Perkins, Schiller, *A simple proof of rapid mixing on random
regular graphs beyond uniqueness*, arXiv:2606.27545 (version of 2026-11-03, sha256 dfc58c3b…), proof of Theorem 1.2, pp.8–9.

Under the hypotheses of Theorem 1.2 (µ fully supported on a non-empty downward-closed `X`,
`δ ∈ (0,1)`, every `M_σ`, `σ ∈ X`, positive semidefinite), for every `f`, with
`ψ_σ(v) := D⁺_v f(σ)`:

1. `⟨Lf, Lf⟩_µ + δ⟨f, Lf⟩_µ ≥ E_µ[ Σ_{u,v} ((1 − δ) r_v(σ) 1_{u=v} − r_v(σ)(D⁺_v r_u)(σ)) ψ_σ(u) ψ_σ(v) ]`
   (p.8);
2. `⟨Lf, Lf⟩_µ + δ⟨f, Lf⟩_µ ≥ 0` (p.9).

**Formalization Note** The matrix in the expectation is `Mmat µ δ σ` (3), so the double sum is
`ψ_σ ⬝ᵥ M_σ *ᵥ ψ_σ`. Positive semidefiniteness is the quadratic-form condition. -/
theorem theorem_1_2_display {V : Type*} [Fintype V] [DecidableEq V] (μ : (V → Bool) → ℝ)
    (hμ : IsDownClosedLaw μ) (δ : ℝ) (hδ0 : 0 < δ) (hδ1 : δ < 1)
    (hM : ∀ σ, 0 < μ σ → ∀ x : V → ℝ, 0 ≤ x ⬝ᵥ (Mmat μ δ σ *ᵥ x)) (f : (V → Bool) → ℝ) :
    expect μ (fun σ => (fun v => Dplus v f σ) ⬝ᵥ (Mmat μ δ σ *ᵥ fun v => Dplus v f σ)) ≤
        ip μ (gen μ f) (gen μ f) + δ * ip μ f (gen μ f) ∧
      0 ≤ ip μ (gen μ f) (gen μ f) + δ * ip μ f (gen μ f) := by sorry

end HardCoreBochner
