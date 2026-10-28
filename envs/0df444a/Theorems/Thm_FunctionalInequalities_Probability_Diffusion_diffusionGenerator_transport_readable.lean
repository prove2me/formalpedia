-- Prove2me | Theorems.Thm_FunctionalInequalities_Probability_Diffusion_diffusionGenerator_transport_readable
-- name    : FunctionalInequalities.Probability.Diffusion.diffusionGenerator_transport_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:10:32.984851+00:00
-- url     : https://prove2.me/theorems/9a1d8a25-4515-49cd-b4f2-f5f23338d6b2
-- title:
--   Diffusion Generator Under Linear Coordinate Transport
-- statement:
--   Let $V,V'$ be finite-dimensional real normed spaces, let $\Phi:V\simeq V'$ be a continuous linear equivalence, let $b:V\to V$, $\sigma:V\to\mathrm{Fin}(d)\to V$, and $F:V\to\mathbb R$. For every $x\in V$, the generator is invariant under transport:
--
--   $$
--   \mathcal L_{\Phi_*b,\Phi_*\sigma}(F\circ\Phi^{-1})(\Phi x)
--   =\mathcal L_{b,\sigma}F(x).
--   $$
--
--   Here `transportDrift`, `transportNoise`, and `diffusionGenerator` are the Lean definitions involved. No differentiability assumption on $F$ is included in the theorem statement.
--
--   **Original Lean declaration header**
--
--   Within namespace `FunctionalInequalities.Probability.Diffusion`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   theorem diffusionGenerator_transport {V' : Type*} [NormedAddCommGroup V'] [NormedSpace ℝ V']
--       {d : ℕ} (Φ : V ≃L[ℝ] V') (b : V → V) (σ : V → Fin d → V) (F : V → ℝ) (x : V) :
--       diffusionGenerator (transportDrift Φ b) (transportNoise Φ σ) (F ∘ Φ.symm) (Φ x) =
--         diffusionGenerator b σ F x
--   ```
--
--   **Module navigation**
--
--   Module: [`Probability/Diffusion/Generator`](https://prove2.me/theorems/ee0b5d14-6576-4335-ba28-d45bb3683eb2).
--
--   Next: [`diffusionGenerator_comp`](https://prove2.me/theorems/04591c87-9e70-47ad-8801-7d7fe84bea55).
--
--   [Source excerpt, lines 46–49](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/Probability/Diffusion/Generator.lean#L46-L49) · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Probability/Diffusion/Generator.lean#L44-L72 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Probability.Diffusion.Generator`, declaration `FunctionalInequalities.Probability.Diffusion.diffusionGenerator_transport`; the repository is private at upload time).

import Definitions.Def_KLSModular_FunctionalInequalities_Probability_Diffusion_Generator

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]

theorem FunctionalInequalities.Probability.Diffusion.diffusionGenerator_transport_readable {V' : Type*} [NormedAddCommGroup V'] [NormedSpace ℝ V']
    {d : ℕ} (Φ : V ≃L[ℝ] V') (b : V → V) (σ : V → Fin d → V) (F : V → ℝ) (x : V) :
    diffusionGenerator (transportDrift Φ b) (transportNoise Φ σ) (F ∘ Φ.symm) (Φ x) =
      diffusionGenerator b σ F x := by sorry
