-- Prove2me | Theorems.Thm_MasulloGRH_weakDual_polar_isCompact_of_nhds
-- name    : MasulloGRH.weakDual_polar_isCompact_of_nhds
-- status  : Proved
-- author  : @marozols
-- created : 2026-11-20T23:37:59.759741+00:00
-- url     : https://prove2.me/theorems/e91c2b16-dabe-4339-bcc9-5ce1f939b0d9
-- title:
--   Banach–Alaoglu for a neighborhood in a complex topological vector space
-- statement:
--   Let $E$ be a complex topological vector space, and let $V$ be any neighborhood of zero. Its polar $$V^\circ=\{f\in E': |f(x)|\leq 1\text{ for every }x\in V\}$$ is compact in the weak-star topology $\sigma(E',E)$. This gives compact disks in duals even when the topology of $E$ requires many seminorms.
-- source:
--   N. Bourbaki, Topological Vector Spaces, Chapter III, §3 (equicontinuous sets of linear forms). See also A. Grothendieck, Topological Vector Spaces, Chapter II §11, Theorem 6 (weak relative compactness of equicontinuous subsets), https://djvu.online/file/q9VXVQUMLaWE8 .

import Mathlib.Analysis.Normed.Module.WeakDual
import Mathlib.Analysis.Complex.Basic

open Set Filter Topology Bornology

namespace MasulloGRH

theorem weakDual_polar_isCompact_of_nhds (E : Type*) [AddCommGroup E] [Module ℂ E]
    [TopologicalSpace E] [IsTopologicalAddGroup E] [ContinuousSMul ℂ E]
    (V : Set E) (hV : V ∈ 𝓝 (0:E)) : IsCompact (WeakDual.polar ℂ V) := by sorry

end MasulloGRH
