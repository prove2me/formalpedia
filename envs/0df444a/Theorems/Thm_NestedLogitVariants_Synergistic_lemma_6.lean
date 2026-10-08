-- Prove2me | Theorems.Thm_NestedLogitVariants_Synergistic_lemma_6
-- name    : NestedLogitVariants.Synergistic.lemma_6
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-05T21:40:52.107974+00:00
-- url     : https://prove2.me/theorems/eba2542a-5868-4e9f-b851-937902a39b76
-- title:
--   Lemma 6, p. 21 — problem (8) has an optimal solution that is a nested-by-revenue assortment with at most one fractional product
-- statement:
--   Fix a nest $i$ of an instance with fully-captured nests and a real number $x$, and assume $n \ge 1$. The maximization problem
--
--   $$\max_{z_i \in [0,1]^n} \Big(\sum_{j \in N} v_{ij} z_{ij}\Big)^{\gamma_i} \left[\frac{\sum_{j\in N} r_{ij} v_{ij} z_{ij}}{\sum_{j\in N} v_{ij} z_{ij}} - x\right] \tag{8}$$
--
--   has an optimal solution $z^*_i$ of the form
--
--   $$z^*_{i1} = \dots = z^*_{i,k-1} = 1, \quad z^*_{ik} \in [0,1], \quad z^*_{i,k+1} = \dots = z^*_{in} = 0$$
--
--   for some $k \in \{1, \dots, n\}$. In particular the maximum in (8) is attained.
--
--   Up to one fractional component, a nested-by-revenue assortment solves the inner problem of (7); this is why the nested-by-revenue assortments are almost sufficient for problem (7).
--
--   **Formalization Note** The standing assumptions are those of the model (see the Model definition) and of §4: every nest is fully captured, $v_{i0} = 0$, and $\gamma_i > 1$ for some nest $i$ (p. 16). Products are indexed from $0$ (`Fin n`), so $k$ is a `Fin n`. The value of the objective at $z_i = 0$ is $0$ (real power $0^{\gamma_i} = 0$ and $0/0 = 0$). The condition $n \ge 1$ is the range $k = 1, \dots, n$ of the page.
-- source:
--   Davis, Gallego, Topaloglu, Assortment optimization under variants of the nested logit model, revised manuscript of June 18, 2013 (published Oper. Res. 62(2), 2014, DOI 10.1287/opre.2014.1256), p. 21, Lemma 6 and display (8)

import Mathlib
import Definitions.Def_NestedLogitVariants_Synergistic_Relaxation

namespace NestedLogitVariants.Synergistic

/-- Lemma 6, p. 21: for every nest `i` and every `x`, problem (8) has an optimal solution `z*` of the
form `z*_1 = ⋯ = z*_{k−1} = 1`, `z*_k ∈ [0, 1]`, `z*_{k+1} = ⋯ = z*_n = 0` for some product `k`. -/
theorem lemma_6 {ι : Type*} [Fintype ι] [DecidableEq ι] {n : ℕ} (I : Instance ι n)
    (hI : I.Standing) (hfc : ∀ i, I.vnp i = 0) (hsyn : ∃ i, 1 < I.γ i)
    (hn1 : 0 < n) (i : ι) (x : ℝ) :
    ∃ z ∈ NestedLogitVariants.LP.box n, (∀ z' ∈ NestedLogitVariants.LP.box n, F8 I i z' x ≤ F8 I i z x) ∧ ∃ k : Fin n, IsFracPrefix z k := by sorry

end NestedLogitVariants.Synergistic
