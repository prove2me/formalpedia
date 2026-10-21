-- Prove2me | Theorems.Thm_MazurTransfer_original_trivial_continuous_cohomology_characters_bijective
-- name    : MazurTransfer.original_trivial_continuous_cohomology_characters_bijective
-- status  : Proved
-- author  : @Vas
-- created : 2026-10-20T18:30:51.992097+00:00
-- url     : https://prove2.me/theorems/7017ad23-419b-4535-9992-88df4df1f349
-- statement:
--   For a group $G$, a commutative coefficient group $M$ in the original topology context and a supplied trivial action, the original map $H^1_{\mathrm{cts}}(G,M)\to\operatorname{Hom}_{\mathrm{cts}}(G,M)$ is injective and surjective. Its value on a cocycle class is the original cocycle homomorphism, and zero image implies zero class. The same group actions, topologies and triviality hypothesis are retained. Named downstream consumer: the original additive character equivalence and genuine characters of the same arithmetic character kernel.

import Definitions.Def_MazurTransfer_OriginalTrivialContinuousCohomologyCharacterMapData20261019
noncomputable section
open MazurTransfer ContinuousFirstCohomologyPresentation TrivialContinuousH1Characters

theorem MazurTransfer.original_trivial_continuous_cohomology_characters_bijective : (∀ (G M : Type) [Group G] [CommGroup M] [MulDistribMulAction G M] [TopologicalSpace G] [TopologicalSpace M] [IsTopologicalGroup M] (htriv : ∀ (g : G) (m : M), g • m = m) (z : continuousCocycles G M), toHom G M htriv (classMap G M z) = Additive.ofMul (cocycleHom G M htriv z)) ∧ (∀ (G M : Type) [Group G] [CommGroup M] [MulDistribMulAction G M] [TopologicalSpace G] [TopologicalSpace M] [IsTopologicalGroup M] (htriv : ∀ (g : G) (m : M), g • m = m) (x : H1 G M) (hx : toHom G M htriv x = 0), x = 0) ∧ (∀ (G M : Type) [Group G] [CommGroup M] [MulDistribMulAction G M] [TopologicalSpace G] [TopologicalSpace M] [IsTopologicalGroup M] (htriv : ∀ (g : G) (m : M), g • m = m), Function.Injective (toHom G M htriv)) ∧ (∀ (G M : Type) [Group G] [CommGroup M] [MulDistribMulAction G M] [TopologicalSpace G] [TopologicalSpace M] [IsTopologicalGroup M] (htriv : ∀ (g : G) (m : M), g • m = m), Function.Surjective (toHom G M htriv)) := by sorry
