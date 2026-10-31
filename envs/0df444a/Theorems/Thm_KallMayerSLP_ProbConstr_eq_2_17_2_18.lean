-- Prove2me | Theorems.Thm_KallMayerSLP_ProbConstr_eq_2_17_2_18
-- name    : KallMayerSLP.ProbConstr.eq_2_17_2_18
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T22:12:16.530763+00:00
-- url     : https://prove2.me/theorems/bb4266fb-63c1-4c95-8b8f-3360c0488bc1
-- title:
--   (2.17)–(2.18), p.98 — $\mathcal B(\alpha)$ for a finite discrete distribution
-- statement:
--   Let $\xi$ have the finite discrete distribution given by the realization tableau $(p_i;\hat\xi^i)_{i=1}^N$ with $p_i>0$ and $\sum_i p_i=1$, let $I=\{1,\dots,N\}$ and $K_j=\{x\mid T(\hat\xi^j)x\ge h(\hat\xi^j)\}$. Then for every level $\alpha\in\mathbb R$
--   $$
--   \mathcal B(\alpha)=\bigcup_{\substack{J\subset I\\ \sum_{j\in J}p_j\ge\alpha}}\ \bigcap_{j\in J}\{x\mid T(\hat\xi^j)x\ge h(\hat\xi^j)\}
--   =\bigcup_{\substack{J\subset I\\ \sum_{j\in J}p_j\ge\alpha}}\ \bigcap_{j\in J}K_j .
--   $$
--
--   So the chance-constrained problem over $\mathcal B(\alpha)$ maximizes a linear function over a union of convex polyhedra: a disjunctive program.
--
--   **Formalization Note** $J$ ranges over all subsets of $I$, including $\emptyset$, whose intersection is all of $\mathbb R^n$ (relevant only when $\alpha\le 0$).
--
--   Differences from the source:
--   - generalization: T(ξ), h(ξ) affine in ξ (Notations, p.ix) → T(ξ), h(ξ) arbitrary functions of the realization; reason: only their values at the atoms ξ̂^i enter, and affine data are a special case
--   - encoding: ξ with the finite discrete distribution of the tableau (2.15), indices 1, …, N → τ : RealizationTableau N r with law Σ_i p_i δ_{ξ̂^i}, indices Fin N; reason: the same law; atoms are allowed to coincide, as in the book's tableau
-- source:
--   Kall & Mayer, Stochastic Linear Programming: Models, Theory, and Computation (Kluwer/Springer 2005), Chapter 2, Chapter 2, §2.2, (2.17) and (2.18), p.98 (PDF 108)

import Mathlib
import Definitions.Def_KallMayerSLP_ProbConstr_realizationSet
import Definitions.Def_KallMayerSLP_ProbConstr_feasibleSet
import Definitions.Def_KallMayerSLP_ProbConstr_RealizationTableau_measure

namespace KallMayerSLP.ProbConstr

/-- Representations (2.17)–(2.18) for a finite discrete distribution: with `I = {1, …, N}` and
`K_j = {x | T(ξ̂^j)x ≥ h(ξ̂^j)}`,
`B(α) = ⋃_{J ⊂ I, Σ_{j∈J} p_j ≥ α} ⋂_{j∈J} {x | T(ξ̂^j)x ≥ h(ξ̂^j)} = ⋃_{J ⊂ I, Σ_{j∈J} p_j ≥ α} ⋂_{j∈J} K_j`.

Kall & Mayer 2005, Chapter 2, §2.2, (2.17) and (2.18), p.98 (PDF 108).

**Formalization Note.** `ξ` has the finite discrete distribution of the realization tableau (2.15)
(`τ.measure = Σ_i p_i · dirac(ξ̂^i)`, `p_i > 0`, `Σ p_i = 1`), indices `Fin N` for `1, …, N`. The data
`T(ξ)`, `h(ξ)` are arbitrary functions of the realization (the book's affine data are a special
case); only their values at the atoms matter. `J` ranges over all subsets of `I`, including `∅` (whose
intersection is all of `ℝ^n`, relevant only when `α ≤ 0`). `K_j` is `realizationSet T h (τ.xi j)`,
so (2.17) and (2.18) are the same set and one equation states both. Every real `α`. -/
theorem eq_2_17_2_18 {N r m n : ℕ} (τ : RealizationTableau N r)
    (T : (Fin r → ℝ) → Matrix (Fin m) (Fin n) ℝ) (h : (Fin r → ℝ) → Fin m → ℝ) (α : ℝ) :
    feasibleSet τ.measure T h α =
      ⋃ (J : Finset (Fin N)) (_ : α ≤ ∑ j ∈ J, τ.p j), ⋂ j ∈ J, realizationSet T h (τ.xi j) := by sorry

end KallMayerSLP.ProbConstr
