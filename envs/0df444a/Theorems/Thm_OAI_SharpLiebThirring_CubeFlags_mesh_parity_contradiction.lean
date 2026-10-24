-- Prove2me | Theorems.Thm_OAI_SharpLiebThirring_CubeFlags_mesh_parity_contradiction
-- name    : OAI.SharpLiebThirring.CubeFlags.mesh_parity_contradiction
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-23T13:58:57.135308+00:00
-- url     : https://prove2.me/theorems/8fe51a53-6680-4da7-95e6-2a1eaae3f119
-- title:
--   Door-to-door parity on an equivariant cubical mesh: a single boundary orbit is impossible (OpenAI Lieb–Thirring)
-- statement:
--   **Setting.** As in `OAI.SharpLiebThirring.CubeFlags.exists_terminal_zero_affine`: $H$ is a group of coordinate sign changes of $\mathbb R^{d+1}$ fixing the time coordinate, $\rho$ is a linear representation of $H$ on a real space $V$, $L : \mathbb R^d \to V$ is a linear isomorphism (so $\dim V = d$), and the affine orbit model lives on the balls of radius $R$ around the $H$-orbit of $(p, 0)$.
--
--   The integer cube grid of $\mathbb R^{d+1}$, scaled by a mesh $h > 0$, is triangulated by its barycentric subdivision. A maximal simplex is a **cubical flag** (`Flag (d+1)`: a base cube, a corner choice and an order of the coordinates). Its $d+2$ vertices are face barycentres (`Flag.vertex`, at the grid points `gridPoint h`), and `Flag.neighbor F j` is the other maximal simplex across the facet opposite vertex $j$. $H$ acts on flags. $D$ is a finite $H$-invariant set of flags, and $a$ assigns a vector of $V$ to each vertex of $D$, $H$-equivariantly. Its affine interpolation on each simplex is the piecewise-linear map whose zeros are counted.
--
--   **Statement.** Assume, with $0 < 2h < R$ and the orbit balls $8R$-separated:
--   - **genericity:** on every flag of $D$, any $d+1$ of the labels are affinely independent, and any $d$ of them are linearly independent;
--   - **freeness:** $H$ acts freely on the grid points of the vertices;
--   - at time $0$, inside the orbit balls, the labels are the values of the affine orbit model with centre $q$;
--   - the flag $F_0 \in D$ is the bottom seed flag at $p$ (`bottomSeed h p`); its neighbour across the facet opposite its last vertex is not in $D$; and a convex combination $w_0$ of its vertices, positive off the last vertex and zero on it, equals $(q, 0)$, so $(q,0)$ lies on that boundary facet;
--   - **boundary control:** whenever the interpolation vanishes on a facet of a flag of $D$ whose neighbour across that facet is not in $D$, that facet is a bottom facet at time $0$ and the zero lies in the orbit balls of radius $R/2$.
--
--   Then these hypotheses are contradictory: the conclusion is `False`.
--
--   This is the combinatorial heart of OpenAI's discrete replacement for the paper's Lemma 5.2 (continuation modulo two), used in the proof of Proposition 5.1: zeros of a generic piecewise-linear map pair up from simplex to simplex, so boundary zeros come in pairs of free orbits, while the hypotheses allow exactly one. Lean: `OAI.SharpLiebThirring.CubeFlags.mesh_parity_contradiction`, OpenAI's lemma of that name (in lean/OAI/Analysis/LiebThirring/BoundaryParity.lean). The definitions (`Flag`, `vertices`, `flagVertex`, `gridPoint`, `bottomSeed`, `Flag.combination`, `orbitBall`, `affineOrbitModel`) come from the definitions bundle `OAIQWSLT000` of this split.
-- source:
--   OpenAI, Sharp one-dimensional Lieb–Thirring constants, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 262; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Sharp-One-Dimensional-Lieb-Thirring-Constants-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/LiebThirring/BoundaryParity.lean (declaration OAI.SharpLiebThirring.CubeFlags.mesh_parity_contradiction)

import Mathlib
import Definitions.Def_OAIQWSLT000

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe u136 u137 u138 u139 u140 u141 u142

noncomputable section
open Finset
noncomputable section
open Finset
noncomputable section
open Finset

namespace SharpLiebThirring.CubeFlags
open Finset SharpLiebThirring.PLParity

lemma mesh_parity_contradiction {d : ℕ} (H : Subgroup (Signs (d + 1)))
    (hHt : ∀ s : H, s.val.val (Fin.last d) = false)
    (D : SubMulAction H (Flag (d + 1))) [Fintype D]
    {V : Type u137} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    (ρ : H →* (V ≃ₗ[ℝ] V)) (L : (Fin d → ℝ) ≃ₗ[ℝ] V)
    (p q : Fin d → ℝ) (R h : ℝ) (hR : 0 < R) (hh : 0 < h) (hhr : 2*h < R)
    (hsep : ∀ g k : H, g ≠ k → 8 * R < dist (g • embedSpatial p) (k • embedSpatial p))
    (a : vertices H D → V) (ha : ∀ s : H, ∀ z, a (s • z) = ρ s (a z))
    (haug : ∀ F : D, ∀ j : Fin (d + 2), LinearIndependent ℝ
      (fun k : {k // k ≠ j} ↦ ((1 : ℝ), a (flagVertex H D F k))))
    (hvec : ∀ F : D, ∀ i j : Fin (d + 2), i ≠ j → LinearIndependent ℝ
      (fun k : {k // k ≠ i ∧ k ≠ j} ↦ a (flagVertex H D F k)))
    (hfree : ∀ z : vertices H D, ∀ s : H, s • gridPoint h z.val = gridPoint h z.val → s = 1)
    (haf : ∀ F : D, ∀ k, gridPoint h (F.val.vertex k) (Fin.last d) = 0 →
      gridPoint h (F.val.vertex k) ∈ orbitBall (G := H) (embedSpatial p) R →
      a (flagVertex H D F k) = affineOrbitModel H ρ L (embedSpatial p) R q (gridPoint h (F.val.vertex k)))
    (F₀ : D) (hF₀ : F₀.val = bottomSeed h p)
    (hout₀ : F₀.val.neighbor (Fin.last (d + 1)) ∉ D)
    (w₀ : Fin (d + 2) → ℝ) (hw₀ : ∀ k, 0 ≤ w₀ k)
    (hwp : ∀ k, k ≠ Fin.last (d + 1) → 0 < w₀ k) (hs₀ : ∑ k, w₀ k = 1)
    (hj₀ : w₀ (Fin.last (d + 1)) = 0)
    (he₀ : (bottomSeed h p).combination h w₀ = embedSpatial q)
    (hbdy : ∀ F : D, ∀ j : Fin (d + 2), F.val.neighbor j ∉ D →
      ∀ w : Fin (d + 2) → ℝ, (∀ k, 0 ≤ w k) → ∑ k, w k = 1 → w j = 0 →
      ∑ k, w k • a (flagVertex H D F k) = 0 →
      j = Fin.last (d + 1) ∧ (F.val.order.symm (Fin.last d)).val = d ∧
      F.val.base (Fin.last d) = 0 ∧ F.val.corner (Fin.last d) = false ∧
      F.val.combination h w ∈ orbitBall (G := H) (embedSpatial p) (R / 2)) : False := by
  sorry

end SharpLiebThirring.CubeFlags

end
end
end

end OAI
end
