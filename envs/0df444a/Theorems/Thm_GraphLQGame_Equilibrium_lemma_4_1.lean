-- Prove2me | Theorems.Thm_GraphLQGame_Equilibrium_lemma_4_1
-- name    : GraphLQGame.Equilibrium.lemma_4_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T12:26:03.629418+00:00
-- url     : https://prove2.me/theorems/b0096dfa-76c8-476c-b738-faae6f1229e8
-- title:
--   Lemma 4.1 — $L$ commutes with every $R_\varphi$, and $\mathrm{Aut}(G)$-equivariant matrices have constant diagonal
-- statement:
--   Let $G$ be transitive on $V=\{1,\dots,n\}$, and for $\varphi\in\mathrm{Aut}(G)$ let $R_\varphi$ be the permutation matrix with $R_\varphi e_i=e_{\varphi(i)}$.
--
--   1. $L R_\varphi=R_\varphi L$ for every $\varphi\in\mathrm{Aut}(G)$.
--   2. If $Y\in\mathbb R^{n\times n}$ commutes with $R_\varphi$ for every $\varphi$, then $Y_{ii}=\frac1n\mathrm{Tr}(Y)$ for all $i$.
--   3. If $Y^1,\dots,Y^n\in\mathbb R^{n\times n}$ satisfy $R_\varphi Y^i=Y^{\varphi(i)}R_\varphi$ for every $\varphi$ and $i$, then $Y^i_{ii}=Y^j_{jj}$ for all $i,j$.
--
--   These symmetry facts are where transitivity enters the proof of Theorem 2.5.
--
--   **Formalization Note** Vertices are `Fin n`; $R_\varphi$ is `autMatrix φ`.
-- source:
--   Lacker, Soret, A case study on stochastic games on large graphs in mean field and sparse regimes, arXiv:2005.14102v2 (2021), Lemma 4.1, p. 23

import Mathlib
import Definitions.Def_GraphLQGame_Equilibrium_Graph

namespace GraphLQGame.Equilibrium

/-- Lacker–Soret, arXiv:2005.14102v2, Lemma 4.1, p. 23. Let `G` be transitive on
`V = {1, …, n}` and let `R_φ` be the permutation matrix with `R_φ e_i = e_{φ(i)}`.
(i) `L` commutes with `R_φ` for each `φ ∈ Aut(G)`.
(ii) If `Y` commutes with every `R_φ`, then `Y_ii = Tr(Y)/n` for all `i`.
(iii) If `R_φ Yⁱ = Y^{φ(i)} R_φ` for every `φ` and `i`, then `Yⁱ_ii = Yʲ_jj` for all `i, j`.

Formalization Note: vertices are `Fin n`; `autMatrix φ` is `R_φ`. -/
theorem lemma_4_1 {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (hT : IsTransitive G) :
    (∀ φ : G ≃g G, lap G * autMatrix φ = autMatrix φ * lap G) ∧
      (∀ Y : Matrix (Fin n) (Fin n) ℝ, (∀ φ : G ≃g G, Y * autMatrix φ = autMatrix φ * Y) →
        ∀ i, Y i i = (n : ℝ)⁻¹ * Y.trace) ∧
      (∀ Y : Fin n → Matrix (Fin n) (Fin n) ℝ,
        (∀ (φ : G ≃g G) (i : Fin n), autMatrix φ * Y i = Y (φ i) * autMatrix φ) →
        ∀ i j, Y i i i = Y j j j) := by sorry

end GraphLQGame.Equilibrium
