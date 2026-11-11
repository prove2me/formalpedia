-- Prove2me | Theorems.Thm_GMSTFramework_LocalStructure_observation_8_3
-- name    : GMSTFramework.LocalStructure.observation_8_3
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T19:03:27.489194+00:00
-- url     : https://prove2.me/theorems/10730325-338a-403c-a44b-5a50704f5344
-- title:
--   Observation 8.3 — a surface configuration of large strength contains an extended $k$-surface-wall with $h$ handles and $c$ crosscaps [GSW25b]
-- statement:
--   (Cited from [GSW25b] as printed in this paper.) Let $k\ge3$ and $\ell,h,c\ge0$ with $\ell=h+c$; let $s\ge k$, $r\ge4k$, $p_i\ge4k$ for all $i\in[\ell]$. Then for every surface configuration $(G,\Omega,\mathcal C,\mathcal R,\mathcal P)$ of strength $(s,r,p_1,\dots,p_\ell)$ with $h$ handle-transactions and $c$ crosscap-transactions, $G$ contains an (extended) $k$-surface-wall $W$ with $h$ handles and $c$ crosscaps as a subgraph such that the base cycles of $W$ are cycles from $\mathcal C$ and the vertical paths of the $k$-wall-segment of $W$ are subpaths of the paths from $\mathcal R$.
--
--   Differences from the source:
--   - encoding: an (extended) k-surface-wall with h handles and c crosscaps → a SurfaceWall G k with signature (h, c, 0, 0); reason: a surface-wall has no flap- or vortex-segments
--   - encoding: "base cycles of W are cycles from C", "subpaths of the paths from R" → each base cycle equals some nest cycle as a subgraph; each vertical path of the wall-segment is a subgraph of some path of R; reason: literal set-theoretic reading
-- source:
--   Gorsky, Protopapas, Wiederrecht, A unifying framework for Graph Minor Structure Theorems with polynomial bounds, STOC 2027 submission (manuscript sha256 b2ee466d…), Observation 8.3, p. 86 (PDF 89)

import Mathlib
import Definitions.Def_GMSTFramework_LocalStructure_Societies
import Definitions.Def_GMSTFramework_LocalStructure_SurfaceWalls

open scoped Classical

namespace GMSTFramework.LocalStructure

/-- Observation 8.3 ([GSW25b]): a surface configuration of large strength contains an extended
`k`-surface-wall with `h` handles and `c` crosscaps built from its nest and radial linkage. -/
theorem observation_8_3 :
    ∀ k ℓ h c : ℕ, 3 ≤ k → ℓ = h + c →
    ∀ (s r : ℕ) (p : Fin ℓ → ℕ), k ≤ s → 4 * k ≤ r → (∀ i, 4 * k ≤ p i) →
    ∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) (Ω : List V)
      (S : SurfaceConfiguration G Ω s r ℓ p), S.HasTypes h c →
      ∃ W : SurfaceWall G k, W.HasSignature h c 0 0 ∧
        (∀ i : Fin k, ∃ j : Fin s, W.baseCycle i = S.nest.C j) ∧
        ∀ i, W.IsWallSeg i → ∀ j < 4 * k, ∃ m, W.verticalPath i j ≤ (S.R.path m).sub := by sorry

end GMSTFramework.LocalStructure
