-- Prove2me | Theorems.Thm_HananyPuder_exists_linearEquiv_pi_youngSpace
-- name    : HananyPuder.exists_linearEquiv_pi_youngSpace
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-05T22:12:50.881194+00:00
-- url     : https://prove2.me/theorems/48f604d2-149b-4106-8896-c73f2ab7ae9f
-- title:
--   Hanany–Puder, Proposition B.2 — every stable representation is a direct sum of representations λ⁽¹⁾[N], …, λ⁽ˢ⁾[N]
-- statement:
--   Let $\pi$ be a stable representation (`StableRep`), defined for $N \ge N_0$ by a character polynomial. Then there are base partitions $\lambda^{(1)}, \dots, \lambda^{(s)}$ (Young diagrams, not necessarily distinct) such that for every $N \ge N_0$ with $N \ge |\lambda^{(j)}| + \lambda^{(j)}_1$ for all $j$, the representation $\pi_N$ on $\mathbb C^{D_N}$ is isomorphic to the direct sum of the representations of $\mathbf S_N$ defined by $\lambda^{(1)}[N], \dots, \lambda^{(s)}[N]$. That is, there is a complex linear isomorphism $e$ from $\mathbb C^{D_N}$ to the product of the spaces `youngSpace N (stableRows λ⁽ʲ⁾ N)` with $e(\pi_N(\sigma)x)_j = \sigma \cdot e(x)_j$ (`youngAct`) for every $\sigma \in \mathbf S_N$, every $x$ and every $j$. Here $|\lambda|$ is the number of cells of $\lambda$ and $\lambda_1$ its first row length, and $\lambda[N] = (N - |\lambda|, \lambda_1, \dots, \lambda_\ell)$ (`stableRows`).
-- source:
--   Chen, C.-F., Garza-Vargas, J., Tropp, J. A. and van Handel, R., A new approach to strong convergence, Ann. of Math. (2) 203 (2026) 555–602, https://doi.org/10.4007/annals.2026.203.2.4 (arXiv:2405.16026v3, whose page numbers are used), p. 14, the proposition of Hanany–Puder cited in §3.4, which cites Hanany, L. and Puder, D., Word measures on symmetric groups, Int. Math. Res. Not. IMRN 2023 (2023) 9221–9297, https://doi.org/10.1093/imrn/rnac084 (arXiv:2009.00897v4), Proposition B.2

import Mathlib
import Definitions.Def_StrongConv
import Definitions.Def_StrongConvG4

open StrongConv

namespace HananyPuder

theorem exists_linearEquiv_pi_youngSpace (π : StableRep) :
    ∃ (s : ℕ) (μ : Fin s → YoungDiagram), ∀ N : ℕ, π.N₀ ≤ N →
      (∀ j, (μ j).cells.card + (μ j).rowLen 0 ≤ N) →
      ∃ e : EuclideanSpace ℂ (Fin (π.dim N)) ≃ₗ[ℂ]
          ((j : Fin s) → youngSpace N (stableRows (μ j) N)),
        ∀ (σ : Equiv.Perm (Fin N)) (x : EuclideanSpace ℂ (Fin (π.dim N))),
          e (Matrix.toEuclideanCLM (𝕜 := ℂ)
              (π.π N σ : Matrix (Fin (π.dim N)) (Fin (π.dim N)) ℂ) x) =
            fun j => youngAct N (stableRows (μ j) N) σ (e x j) := by
  sorry

end HananyPuder
