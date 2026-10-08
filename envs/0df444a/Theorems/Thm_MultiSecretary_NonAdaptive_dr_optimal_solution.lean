-- Prove2me | Theorems.Thm_MultiSecretary_NonAdaptive_dr_optimal_solution
-- name    : MultiSecretary.NonAdaptive.dr_optimal_solution
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-05T08:03:42.225761+00:00
-- url     : https://prove2.me/theorems/91b3f3ec-2bf6-41c8-9970-0a3a1eee16eb
-- title:
--   Remark 2 — s* of (16) solves the deterministic relaxation, DR = Σⱼ aⱼ s*ⱼ, and V*_off ≤ DR
-- statement:
--   Let $0<a_m<\dots<a_1$ and masses $f_j>0$ with $\sum_jf_j=1$, and let $0\le k\le n$. The vector
--   $$s^*_j=\min\{nf_j,(k-n\bar F(a_j))_+\},\qquad j\in[m],$$
--   is feasible for the deterministic relaxation ($0\le s^*_j\le nf_j$, $\sum_js^*_j\le k$), it attains its optimal value,
--   $$DR(n,k)=\sum_{j\in[m]}a_js^*_j,$$
--   and the deterministic relaxation bounds the offline value: $V^*_{\mathrm{off}}(n,k)\le DR(n,k)$.
--
--   The relaxation is the benchmark against which the index policy is measured in Lemma 3, and the gap $DR-V^*_{\mathrm{off}}$ is quantified in Proposition 6.
--
--   **Formalization Note** "Its optimal solution is given by (16)" is formalized as feasibility of $s^*$ plus equality of its objective with $DR$; uniqueness is not claimed. $DR$ is defined as the supremum of the LP, so the identity is not definitional.
-- source:
--   Arlotto, Gurvich, Uniformly Bounded Regret in the Multi-Secretary Problem, arXiv:1710.07719v2, Remark 2, eqs. (15)–(16), pp. 10–11

import Mathlib
import Definitions.Def_MultiSecretary_NonAdaptive_Model

namespace MultiSecretary.NonAdaptive

open Finset

/-- Remark 2 (pp. 10–11): `s*` of (16) is feasible for the deterministic relaxation (15) and attains
its optimal value, and `V*_off(n, k) ≤ DR(n, k)` for all `(n, k) ∈ T`. -/
theorem dr_optimal_solution {m : ℕ} (a f : Fin m → ℝ) (ha : IsValues a) (hf : IsMasses f)
    (n k : ℕ) (hkn : k ≤ n) :
    ((∀ j, 0 ≤ sStar f n k j ∧ sStar f n k j ≤ (n : ℝ) * f j) ∧
      ∑ j, sStar f n k j ≤ (k : ℝ)) ∧
    DR a f n k = ∑ j, a j * sStar f n k j ∧
    Voff a f n k ≤ DR a f n k := by sorry

end MultiSecretary.NonAdaptive
