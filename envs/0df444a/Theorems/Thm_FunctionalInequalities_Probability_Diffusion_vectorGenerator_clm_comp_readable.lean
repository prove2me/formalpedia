-- Prove2me | Theorems.Thm_FunctionalInequalities_Probability_Diffusion_vectorGenerator_clm_comp_readable
-- name    : FunctionalInequalities.Probability.Diffusion.vectorGenerator_clm_comp_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:13:36.38927+00:00
-- url     : https://prove2.me/theorems/caa939ed-b8ae-4cc1-9991-797211b242e5
-- title:
--   Vector Generator Commutation with Continuous Linear Maps
-- statement:
--   This is a compatibility identity for the vector-valued diffusion generator under a continuous linear map.
--
--   Let $V$, $W$, and $W'$ be real normed additive groups and normed spaces, let $d$ be a natural number, let $b:V\to V$ and $\sigma:V\to\operatorname{Fin}(d)\to V$, and let $\ell:W\to W'$ be a continuous linear map. For $G:V\to W$ and $x\in V$, assume that $G$ is twice continuously differentiable at $x$.
--
--   Then, writing `vectorGenerator` for the generator,
--
--   $$
--   \operatorname{vectorGenerator}_{b,\sigma}(\ell\circ G)(x)
--   =\ell\!\left(\operatorname{vectorGenerator}_{b,\sigma}(G)(x)\right).
--   $$
--
--   The result allows generator calculations for vector-valued functions to be transported through continuous linear maps, including trace and coordinate maps.
--
--   **Original Lean declaration header**
--
--   Within namespace `FunctionalInequalities.Probability.Diffusion`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   theorem vectorGenerator_clm_comp (b : V → V) (σ : V → Fin d → V)
--       (ℓ : W →L[ℝ] W') {G : V → W} {x : V} (hG : ContDiffAt ℝ 2 G x) :
--       vectorGenerator b σ (fun y => ℓ (G y)) x = ℓ (vectorGenerator b σ G x)
--   ```
--
--   **Module navigation**
--
--   Module: [`Probability/Diffusion/VectorGenerator`](https://prove2.me/theorems/a27154a7-c41b-4d48-aa0c-9939263debb7).
--
--   [Source excerpt, lines 44–46](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/Probability/Diffusion/VectorGenerator.lean#L44-L46) · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Probability/Diffusion/VectorGenerator.lean#L43-L97 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Probability.Diffusion.VectorGenerator`, declaration `FunctionalInequalities.Probability.Diffusion.vectorGenerator_clm_comp`; the repository is private at upload time).

import Definitions.Def_KLSModular_FunctionalInequalities_Probability_Diffusion_VectorGenerator

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] {d : ℕ}
variable {W W' : Type*}
variable [NormedAddCommGroup W] [NormedSpace ℝ W] [NormedAddCommGroup W'] [NormedSpace ℝ W']

theorem FunctionalInequalities.Probability.Diffusion.vectorGenerator_clm_comp_readable (b : V → V) (σ : V → Fin d → V)
    (ℓ : W →L[ℝ] W') {G : V → W} {x : V} (hG : ContDiffAt ℝ 2 G x) :
    vectorGenerator b σ (fun y => ℓ (G y)) x = ℓ (vectorGenerator b σ G x) := by sorry
