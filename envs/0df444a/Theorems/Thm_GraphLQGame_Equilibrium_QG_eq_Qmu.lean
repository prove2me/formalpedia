-- Prove2me | Theorems.Thm_GraphLQGame_Equilibrium_QG_eq_Qmu
-- name    : GraphLQGame.Equilibrium.QG_eq_Qmu
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T12:26:41.828607+00:00
-- url     : https://prove2.me/theorems/86772066-7f34-4084-bbce-8d167db658ec
-- title:
--   §2.3, p. 8 — $Q_G(x) = (\prod_i(1-x\lambda_i^G))^{1/n} = \exp\int\log(1-x\lambda)\,\mu_G(d\lambda)$
-- statement:
--   Let $G$ be a finite graph on $n\ge1$ vertices without isolated vertices. For every $x\ge0$,
--   $$Q_G(x)=\Big(\prod_{i=1}^n(1-x\lambda_i^G)\Big)^{1/n}=\exp\int_{[-2,0]}\log(1-x\lambda)\,\mu_G(d\lambda)=Q_{\mu_G}(x).$$
--
--   This identifies the function $Q_G$ of Theorem 2.5 with $Q_\mu$ of §3 at $\mu=\mu_G$.
--
--   **Formalization Note** The eigenvalues are the roots of the characteristic polynomial with multiplicity; $n\ge1$ is added (for $n=0$, $\mu_G=0$).
-- source:
--   Lacker, Soret, A case study on stochastic games on large graphs in mean field and sparse regimes, arXiv:2005.14102v2 (2021), §2.3, p. 8, first display; §3, p. 19 ("if µ = µ_G … then Q_µ = Q_G")

import Mathlib
import Definitions.Def_GraphLQGame_Equilibrium_Graph
import Definitions.Def_GraphLQGame_Equilibrium_Equilibrium
import Definitions.Def_GraphLQGame_Equilibrium_Spectral

namespace GraphLQGame.Equilibrium

/-- Lacker–Soret, arXiv:2005.14102v2, §2.3, p. 8, first display (and §3, p. 19, "if µ = µ_G …
then Q_µ = Q_G"): for `x ≥ 0`,
`Q_G(x) = (∏_{i=1}^n (1 − xλ_i^G))^{1/n} = exp ∫_{[−2,0]} log(1 − xλ) µ_G(dλ)`.

Formalization Note: the eigenvalues are the roots of the characteristic polynomial of `L_G` with
multiplicity; `0 < n` is added (for `n = 0`, `µ_G = 0` and the exponential side is `1`). -/
theorem QG_eq_Qmu {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hn : 0 < n)
    (hN : NoIsolated G) (x : ℝ) (hx : 0 ≤ x) :
    QG G x = (((lap G).charpoly.roots.map (fun l => 1 - x * l)).prod) ^ ((n : ℝ)⁻¹) ∧
      QG G x = Qmu (specMeasure G) x := by sorry

end GraphLQGame.Equilibrium
