-- Prove2me | Theorems.Thm_OAI_SharpLiebThirring_CubeFlags_exists_terminal_zero_affine
-- name    : OAI.SharpLiebThirring.CubeFlags.exists_terminal_zero_affine
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-23T13:58:57.811875+00:00
-- url     : https://prove2.me/theorems/05928103-6841-48e2-b721-80f5a219fab5
-- title:
--   Equivariant parity on a slab: a continuation from one free orbit of zeros reaches the top (OpenAI Lieb–Thirring)
-- statement:
--   **Setting.** Points of $\mathbb R^{d+1}$ are written $x = (x', x_{d+1})$, and the last coordinate is read as time. `embedSpatial` is $x' \mapsto (x', 0)$ and `spatial` is $x \mapsto x'$. `Signs (d+1)` is the group of coordinate sign changes of $\mathbb R^{d+1}$: an element is a vector of booleans, and it negates the coordinates marked `true`. $H$ is a subgroup of `Signs (d+1)` that never changes the sign of the time coordinate. $V$ is a finite-dimensional real normed space with an isometric linear representation $\rho$ of $H$, and $L : \mathbb R^d \to V$ is a linear isomorphism. For $p \in \mathbb R^d$ and $R > 0$, `orbitBall` is the set of points within distance $R$ of the $H$-orbit of $(p, 0)$. On it, the affine orbit model (`affineOrbitModel H ρ L (embedSpatial p) R p`) is the equivariant extension of $x \mapsto L(x' - p)$ from the ball around $(p, 0)$ to the balls around its translates $s \cdot (p, 0)$: at a point $x$ of the ball labelled $s$ it is $\rho(s)\,L\bigl((s^{-1}x)' - p\bigr)$.
--
--   **Statement.** Suppose the balls around the orbit points are well separated: $\operatorname{dist}(g\cdot(p,0), k\cdot(p,0)) > 8R$ for $g \ne k$ in $H$. Let $f : \mathbb R^{d+1} \to V$ be continuous on the slab $\{0 \le x_{d+1} \le 1\}$ and $H$-equivariant, $f(s \cdot x) = \rho(s) f(x)$. Assume:
--   - at time $0$, $f$ equals the affine orbit model on the orbit balls, and every zero of $f$ at time $0$ lies in the orbit of $(p, 0)$;
--   - the zero set of $f$ in the slab is compact;
--   - $H$ acts freely on the zeros of $f$ in the slab.
--
--   Then $f$ has a zero at time $1$: $f(x) = 0$ for some $x$ with $x_{d+1} = 1$.
--
--   This is the parity step of the paper's proof of Proposition 5.1 (connecting path): at the initial parameter there is exactly one orbit of zeros, and the paper concludes that a terminal zero exists by its Lemma 5.2 (continuation modulo two), a regular-value argument applied to the quotient by row signs. OpenAI's Lean replaces the regular-value argument with a combinatorial one on a fine cubical triangulation (see `OAI.SharpLiebThirring.CubeFlags.mesh_parity_contradiction`). Lean: `OAI.SharpLiebThirring.CubeFlags.exists_terminal_zero_affine`, OpenAI's lemma of that name (in lean/OAI/Analysis/LiebThirring/BoundaryParity.lean). The definitions (`Signs`, `embedSpatial`, `orbitBall`, `affineOrbitModel`) come from the definitions bundle `OAIQWSLT000` of this split.
-- source:
--   OpenAI, Sharp one-dimensional Lieb–Thirring constants, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 262; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Sharp-One-Dimensional-Lieb-Thirring-Constants-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/LiebThirring/BoundaryParity.lean (declaration OAI.SharpLiebThirring.CubeFlags.exists_terminal_zero_affine)

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

theorem exists_terminal_zero_affine {d : ℕ}
    (H : Subgroup (Signs (d + 1))) (hHt : ∀ s : H, s.val.val (Fin.last d) = false)
    {V : Type u142} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    (ρ : H →* (V ≃ₗ[ℝ] V)) (L : (Fin d → ℝ) ≃ₗ[ℝ] V)
    (hρ : ∀ s : H, ∀ v : V, ‖ρ s v‖ = ‖v‖)
    (p : Fin d → ℝ) (R : ℝ) (hR : 0 < R)
    (hsep : ∀ g k : H, g ≠ k → 8 * R < dist (g • embedSpatial p) (k • embedSpatial p))
    (f : (Fin (d + 1) → ℝ) → V)
    (hf : ContinuousOn f {x | x (Fin.last d) ∈ Set.Icc (0 : ℝ) 1})
    (hfe : ∀ s : H, ∀ x, f (s • x) = ρ s (f x))
    (hmodel : ∀ x, x (Fin.last d) = 0 → x ∈ orbitBall (G := H) (embedSpatial p) R →
      f x = affineOrbitModel H ρ L (embedSpatial p) R p x)
    (hz0 : ∀ x, x (Fin.last d) = 0 → f x = 0 → ∃ s : H, s • embedSpatial p = x)
    (hK : IsCompact {x | x (Fin.last d) ∈ Set.Icc (0 : ℝ) 1 ∧ f x = 0})
    (hfree : ∀ x, x (Fin.last d) ∈ Set.Icc (0 : ℝ) 1 → f x = 0 →
      ∀ s : H, s • x = x → s = 1) :
    ∃ x : Fin (d + 1) → ℝ, x (Fin.last d) = 1 ∧ f x = 0 := by
  sorry

end SharpLiebThirring.CubeFlags

end
end
end

end OAI
end
